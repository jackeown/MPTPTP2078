%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1874+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:36 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 222 expanded)
%              Number of leaves         :   33 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 ( 608 expanded)
%              Number of equality atoms :   25 ( 110 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_tarski(A_16),B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_47,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_106,plain,(
    ! [B_50,A_51] :
      ( v1_xboole_0(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_106])).

tff(c_116,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_112])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4,plain,(
    ! [B_5,A_4] : k3_xboole_0(B_5,A_4) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_153,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_2'),B_57,'#skF_3') = k3_xboole_0(B_57,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_147])).

tff(c_163,plain,(
    ! [A_60,C_61,B_62] :
      ( k9_subset_1(A_60,C_61,B_62) = k9_subset_1(A_60,B_62,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_167,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_2'),B_62,'#skF_3') = k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_62) ),
    inference(resolution,[status(thm)],[c_40,c_163])).

tff(c_170,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_62) = k3_xboole_0(B_62,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_167])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_506,plain,(
    ! [A_102,B_103,C_104] :
      ( k9_subset_1(u1_struct_0(A_102),B_103,k2_pre_topc(A_102,C_104)) = C_104
      | ~ r1_tarski(C_104,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_860,plain,(
    ! [A_129,B_130,A_131] :
      ( k9_subset_1(u1_struct_0(A_129),B_130,k2_pre_topc(A_129,A_131)) = A_131
      | ~ r1_tarski(A_131,B_130)
      | ~ v2_tex_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ r1_tarski(A_131,u1_struct_0(A_129)) ) ),
    inference(resolution,[status(thm)],[c_20,c_506])).

tff(c_867,plain,(
    ! [A_131] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',A_131)) = A_131
      | ~ r1_tarski(A_131,'#skF_3')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_131,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_860])).

tff(c_872,plain,(
    ! [A_131] :
      ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',A_131)) = A_131
      | ~ r1_tarski(A_131,'#skF_3')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_131,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_4,c_170,c_867])).

tff(c_874,plain,(
    ! [A_132] :
      ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',A_132)) = A_132
      | ~ r1_tarski(A_132,'#skF_3')
      | ~ r1_tarski(A_132,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_872])).

tff(c_897,plain,(
    ! [A_133] :
      ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k1_tarski(A_133))) = k1_tarski(A_133)
      | ~ r1_tarski(k1_tarski(A_133),'#skF_3')
      | ~ r2_hidden(A_133,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_874])).

tff(c_117,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_126,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_117])).

tff(c_131,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_126])).

tff(c_32,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) != k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_132,plain,(
    k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_32])).

tff(c_171,plain,(
    k3_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_4')),'#skF_3') != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_132])).

tff(c_172,plain,(
    k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_171])).

tff(c_908,plain,
    ( ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_172])).

tff(c_910,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_932,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_910])).

tff(c_935,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_932])).

tff(c_937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_935])).

tff(c_938,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_942,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_938])).

tff(c_946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_942])).

%------------------------------------------------------------------------------
