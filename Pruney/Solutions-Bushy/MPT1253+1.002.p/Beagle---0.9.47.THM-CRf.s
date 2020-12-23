%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1253+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:39 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 163 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 293 expanded)
%              Number of equality atoms :   19 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(c_24,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_42,c_8])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,(
    ! [A_42,B_43,C_44] :
      ( k9_subset_1(A_42,B_43,C_44) = k3_xboole_0(B_43,C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_179,plain,(
    ! [B_58,B_59,A_60] :
      ( k9_subset_1(B_58,B_59,A_60) = k3_xboole_0(B_59,A_60)
      | ~ r1_tarski(A_60,B_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_59])).

tff(c_197,plain,(
    ! [A_61,B_62] : k9_subset_1(A_61,B_62,A_61) = k3_xboole_0(B_62,A_61) ),
    inference(resolution,[status(thm)],[c_47,c_179])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ! [B_43] : k9_subset_1(u1_struct_0('#skF_2'),B_43,'#skF_3') = k3_xboole_0(B_43,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_88,plain,(
    ! [A_46,C_47,B_48] :
      ( k9_subset_1(A_46,C_47,B_48) = k9_subset_1(A_46,B_48,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_94,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_2'),B_48,'#skF_3') = k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_48) ),
    inference(resolution,[status(thm)],[c_28,c_88])).

tff(c_98,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_48) = k3_xboole_0(B_48,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_94])).

tff(c_204,plain,(
    k3_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_xboole_0('#skF_3',u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_98])).

tff(c_53,plain,(
    ! [A_36,B_37,C_38] :
      ( m1_subset_1(k9_subset_1(A_36,B_37,C_38),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_57,plain,(
    ! [A_36,B_37,C_38] :
      ( r1_tarski(k9_subset_1(A_36,B_37,C_38),A_36)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(resolution,[status(thm)],[c_53,c_16])).

tff(c_325,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k3_xboole_0(B_66,A_67),A_67)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_57])).

tff(c_333,plain,
    ( r1_tarski(k3_xboole_0('#skF_3',u1_struct_0('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_325])).

tff(c_361,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_404,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_361])).

tff(c_408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_404])).

tff(c_410,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_236,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,B_64) = B_64
      | ~ v4_pre_topc(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_253,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_236])).

tff(c_264,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_253])).

tff(c_745,plain,(
    ! [A_96,B_97] :
      ( k9_subset_1(u1_struct_0(A_96),k2_pre_topc(A_96,B_97),k2_pre_topc(A_96,k3_subset_1(u1_struct_0(A_96),B_97))) = k2_tops_1(A_96,B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_760,plain,
    ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_745])).

tff(c_764,plain,(
    k3_xboole_0(k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_98,c_760])).

tff(c_207,plain,(
    ! [B_62,A_61] :
      ( r1_tarski(k3_xboole_0(B_62,A_61),A_61)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_57])).

tff(c_802,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_207])).

tff(c_823,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_802])).

tff(c_825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_823])).

%------------------------------------------------------------------------------
