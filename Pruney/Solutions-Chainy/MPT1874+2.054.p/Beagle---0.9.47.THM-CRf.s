%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:44 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 159 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 442 expanded)
%              Number of equality atoms :   17 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_83,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_46,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_131,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k1_tarski(A_52),k1_zfmisc_1(B_53))
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_135,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_131,c_28])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_98,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_98])).

tff(c_107,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_111,plain,(
    k3_xboole_0('#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_106,c_107])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_119,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,u1_struct_0('#skF_4'))
      | ~ r2_hidden(D_6,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_4])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1405,plain,(
    ! [A_215,B_216,C_217] :
      ( k9_subset_1(u1_struct_0(A_215),B_216,k2_pre_topc(A_215,C_217)) = C_217
      | ~ r1_tarski(C_217,B_216)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ v2_tex_2(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9138,plain,(
    ! [A_545,B_546,A_547] :
      ( k9_subset_1(u1_struct_0(A_545),B_546,k2_pre_topc(A_545,A_547)) = A_547
      | ~ r1_tarski(A_547,B_546)
      | ~ v2_tex_2(B_546,A_545)
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ l1_pre_topc(A_545)
      | ~ v2_pre_topc(A_545)
      | v2_struct_0(A_545)
      | ~ r1_tarski(A_547,u1_struct_0(A_545)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1405])).

tff(c_9148,plain,(
    ! [A_547] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_547)) = A_547
      | ~ r1_tarski(A_547,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_547,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_52,c_9138])).

tff(c_9154,plain,(
    ! [A_547] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_547)) = A_547
      | ~ r1_tarski(A_547,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_547,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_9148])).

tff(c_9156,plain,(
    ! [A_548] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_548)) = A_548
      | ~ r1_tarski(A_548,'#skF_5')
      | ~ r1_tarski(A_548,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_9154])).

tff(c_145,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ v1_xboole_0(C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_154,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_60,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_145])).

tff(c_155,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_156,plain,(
    ! [A_61,B_62] :
      ( k6_domain_1(A_61,B_62) = k1_tarski(B_62)
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_172,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_185,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_172])).

tff(c_44,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_186,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_44])).

tff(c_9185,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9156,c_186])).

tff(c_9189,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9185])).

tff(c_9193,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_135,c_9189])).

tff(c_9196,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_119,c_9193])).

tff(c_9200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_9196])).

tff(c_9201,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_9185])).

tff(c_9205,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_135,c_9201])).

tff(c_9209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_9205])).

tff(c_9210,plain,(
    ! [A_60] : ~ r2_hidden(A_60,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_9213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9210,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.57  
% 9.84/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.57  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 9.84/3.57  
% 9.84/3.57  %Foreground sorts:
% 9.84/3.57  
% 9.84/3.57  
% 9.84/3.57  %Background operators:
% 9.84/3.57  
% 9.84/3.57  
% 9.84/3.57  %Foreground operators:
% 9.84/3.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.84/3.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.84/3.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.84/3.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.84/3.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.84/3.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.84/3.57  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.84/3.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.84/3.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.84/3.57  tff('#skF_5', type, '#skF_5': $i).
% 9.84/3.57  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.84/3.57  tff('#skF_6', type, '#skF_6': $i).
% 9.84/3.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.84/3.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.84/3.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.57  tff('#skF_4', type, '#skF_4': $i).
% 9.84/3.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.84/3.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.84/3.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.84/3.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.84/3.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.84/3.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.84/3.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.84/3.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.84/3.57  
% 9.84/3.59  tff(f_103, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 9.84/3.59  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 9.84/3.59  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.84/3.59  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.84/3.59  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.84/3.59  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 9.84/3.59  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 9.84/3.59  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 9.84/3.59  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_131, plain, (![A_52, B_53]: (m1_subset_1(k1_tarski(A_52), k1_zfmisc_1(B_53)) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.84/3.59  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.84/3.59  tff(c_135, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_131, c_28])).
% 9.84/3.59  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_98, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.84/3.59  tff(c_106, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_98])).
% 9.84/3.59  tff(c_107, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.84/3.59  tff(c_111, plain, (k3_xboole_0('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(resolution, [status(thm)], [c_106, c_107])).
% 9.84/3.59  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.59  tff(c_119, plain, (![D_6]: (r2_hidden(D_6, u1_struct_0('#skF_4')) | ~r2_hidden(D_6, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_4])).
% 9.84/3.59  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_50, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_30, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.84/3.59  tff(c_1405, plain, (![A_215, B_216, C_217]: (k9_subset_1(u1_struct_0(A_215), B_216, k2_pre_topc(A_215, C_217))=C_217 | ~r1_tarski(C_217, B_216) | ~m1_subset_1(C_217, k1_zfmisc_1(u1_struct_0(A_215))) | ~v2_tex_2(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.84/3.59  tff(c_9138, plain, (![A_545, B_546, A_547]: (k9_subset_1(u1_struct_0(A_545), B_546, k2_pre_topc(A_545, A_547))=A_547 | ~r1_tarski(A_547, B_546) | ~v2_tex_2(B_546, A_545) | ~m1_subset_1(B_546, k1_zfmisc_1(u1_struct_0(A_545))) | ~l1_pre_topc(A_545) | ~v2_pre_topc(A_545) | v2_struct_0(A_545) | ~r1_tarski(A_547, u1_struct_0(A_545)))), inference(resolution, [status(thm)], [c_30, c_1405])).
% 9.84/3.59  tff(c_9148, plain, (![A_547]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_547))=A_547 | ~r1_tarski(A_547, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_547, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_52, c_9138])).
% 9.84/3.59  tff(c_9154, plain, (![A_547]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_547))=A_547 | ~r1_tarski(A_547, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_547, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_9148])).
% 9.84/3.59  tff(c_9156, plain, (![A_548]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_548))=A_548 | ~r1_tarski(A_548, '#skF_5') | ~r1_tarski(A_548, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_9154])).
% 9.84/3.59  tff(c_145, plain, (![C_58, B_59, A_60]: (~v1_xboole_0(C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.84/3.59  tff(c_154, plain, (![A_60]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_60, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_145])).
% 9.84/3.59  tff(c_155, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_154])).
% 9.84/3.59  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_156, plain, (![A_61, B_62]: (k6_domain_1(A_61, B_62)=k1_tarski(B_62) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.84/3.59  tff(c_172, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_156])).
% 9.84/3.59  tff(c_185, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_155, c_172])).
% 9.84/3.59  tff(c_44, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.59  tff(c_186, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_44])).
% 9.84/3.59  tff(c_9185, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9156, c_186])).
% 9.84/3.59  tff(c_9189, plain, (~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_9185])).
% 9.84/3.59  tff(c_9193, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_135, c_9189])).
% 9.84/3.59  tff(c_9196, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_119, c_9193])).
% 9.84/3.59  tff(c_9200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_9196])).
% 9.84/3.59  tff(c_9201, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_9185])).
% 9.84/3.59  tff(c_9205, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_135, c_9201])).
% 9.84/3.59  tff(c_9209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_9205])).
% 9.84/3.59  tff(c_9210, plain, (![A_60]: (~r2_hidden(A_60, '#skF_5'))), inference(splitRight, [status(thm)], [c_154])).
% 9.84/3.59  tff(c_9213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9210, c_46])).
% 9.84/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.59  
% 9.84/3.59  Inference rules
% 9.84/3.59  ----------------------
% 9.84/3.59  #Ref     : 0
% 9.84/3.59  #Sup     : 2647
% 9.84/3.59  #Fact    : 0
% 9.84/3.59  #Define  : 0
% 9.84/3.59  #Split   : 9
% 9.84/3.59  #Chain   : 0
% 9.84/3.59  #Close   : 0
% 9.84/3.59  
% 9.84/3.59  Ordering : KBO
% 9.84/3.59  
% 9.84/3.59  Simplification rules
% 9.84/3.59  ----------------------
% 9.84/3.59  #Subsume      : 645
% 9.84/3.59  #Demod        : 267
% 9.84/3.59  #Tautology    : 110
% 9.84/3.59  #SimpNegUnit  : 9
% 9.84/3.59  #BackRed      : 10
% 9.84/3.59  
% 9.84/3.59  #Partial instantiations: 0
% 9.84/3.59  #Strategies tried      : 1
% 9.84/3.59  
% 9.84/3.59  Timing (in seconds)
% 9.84/3.59  ----------------------
% 9.84/3.59  Preprocessing        : 0.34
% 9.84/3.59  Parsing              : 0.17
% 9.84/3.59  CNF conversion       : 0.03
% 9.84/3.59  Main loop            : 2.50
% 9.84/3.59  Inferencing          : 0.59
% 9.84/3.59  Reduction            : 0.52
% 9.84/3.59  Demodulation         : 0.36
% 9.84/3.59  BG Simplification    : 0.13
% 9.84/3.59  Subsumption          : 1.05
% 9.84/3.59  Abstraction          : 0.18
% 9.84/3.59  MUC search           : 0.00
% 9.84/3.59  Cooper               : 0.00
% 9.84/3.59  Total                : 2.86
% 9.84/3.59  Index Insertion      : 0.00
% 9.84/3.59  Index Deletion       : 0.00
% 9.84/3.59  Index Matching       : 0.00
% 9.84/3.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
