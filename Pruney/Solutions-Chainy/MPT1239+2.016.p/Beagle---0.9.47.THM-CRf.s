%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:43 EST 2020

% Result     : Theorem 39.20s
% Output     : CNFRefutation 39.31s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 161 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 294 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_14])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_11,B_12] : k2_xboole_0(k4_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(k2_xboole_0(A_59,B_61),C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    ! [A_64,B_65,B_66] : r1_tarski(A_64,k2_xboole_0(k2_xboole_0(A_64,B_65),B_66)) ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_272,plain,(
    ! [A_73,B_74,B_75] : r1_tarski(k4_xboole_0(A_73,B_74),k2_xboole_0(A_73,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_158])).

tff(c_283,plain,(
    ! [B_74] : r1_tarski(k4_xboole_0('#skF_2',B_74),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_272])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1539,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(k1_tops_1(A_171,B_172),B_172)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1992,plain,(
    ! [A_184,A_185] :
      ( r1_tarski(k1_tops_1(A_184,A_185),A_185)
      | ~ l1_pre_topc(A_184)
      | ~ r1_tarski(A_185,u1_struct_0(A_184)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1539])).

tff(c_4960,plain,(
    ! [A_328,A_329] :
      ( k2_xboole_0(k1_tops_1(A_328,A_329),A_329) = A_329
      | ~ l1_pre_topc(A_328)
      | ~ r1_tarski(A_329,u1_struct_0(A_328)) ) ),
    inference(resolution,[status(thm)],[c_1992,c_14])).

tff(c_5014,plain,(
    ! [B_74] :
      ( k2_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',B_74)),k4_xboole_0('#skF_2',B_74)) = k4_xboole_0('#skF_2',B_74)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_283,c_4960])).

tff(c_95568,plain,(
    ! [B_2046] : k2_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',B_2046)),k4_xboole_0('#skF_2',B_2046)) = k4_xboole_0('#skF_2',B_2046) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5014])).

tff(c_131,plain,(
    ! [A_59,B_61] : r1_tarski(A_59,k2_xboole_0(A_59,B_61)) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_95858,plain,(
    ! [B_2047] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',B_2047)),k4_xboole_0('#skF_2',B_2047)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95568,c_131])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1546,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1539])).

tff(c_1553,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1546])).

tff(c_97,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_xboole_0(A_51,C_52)
      | ~ r1_tarski(A_51,k4_xboole_0(B_53,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [B_53,C_52] : r1_xboole_0(k4_xboole_0(B_53,C_52),C_52) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_1223,plain,(
    ! [A_148,C_149,B_150,D_151] :
      ( r1_xboole_0(A_148,C_149)
      | ~ r1_xboole_0(B_150,D_151)
      | ~ r1_tarski(C_149,D_151)
      | ~ r1_tarski(A_148,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3999,plain,(
    ! [A_282,C_283,C_284,B_285] :
      ( r1_xboole_0(A_282,C_283)
      | ~ r1_tarski(C_283,C_284)
      | ~ r1_tarski(A_282,k4_xboole_0(B_285,C_284)) ) ),
    inference(resolution,[status(thm)],[c_107,c_1223])).

tff(c_4155,plain,(
    ! [A_282,B_285] :
      ( r1_xboole_0(A_282,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_282,k4_xboole_0(B_285,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1553,c_3999])).

tff(c_96122,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_95858,c_4155])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k4_xboole_0(B_18,C_19))
      | ~ r1_xboole_0(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1544,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1539])).

tff(c_1550,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1544])).

tff(c_1563,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1550,c_14])).

tff(c_152,plain,(
    ! [A_6,B_7,B_63] : r1_tarski(A_6,k2_xboole_0(k2_xboole_0(A_6,B_7),B_63)) ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_1648,plain,(
    ! [B_173] : r1_tarski(k1_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',B_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_152])).

tff(c_577,plain,(
    ! [A_102,B_103,C_104] :
      ( k7_subset_1(A_102,B_103,C_104) = k4_xboole_0(B_103,C_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_584,plain,(
    ! [B_24,A_23,C_104] :
      ( k7_subset_1(B_24,A_23,C_104) = k4_xboole_0(A_23,C_104)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_26,c_577])).

tff(c_86719,plain,(
    ! [B_1932,C_1933] : k7_subset_1(k2_xboole_0('#skF_2',B_1932),k1_tops_1('#skF_1','#skF_2'),C_1933) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_1933) ),
    inference(resolution,[status(thm)],[c_1648,c_584])).

tff(c_86745,plain,(
    ! [C_1933] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_1933) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_1933) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_86719])).

tff(c_585,plain,(
    ! [C_104] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_104) = k4_xboole_0('#skF_2',C_104) ),
    inference(resolution,[status(thm)],[c_36,c_577])).

tff(c_32,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_587,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_32])).

tff(c_87040,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86745,c_587])).

tff(c_87975,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_87040])).

tff(c_108286,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96122,c_87975])).

tff(c_108295,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_108286])).

tff(c_108300,plain,(
    ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_16,c_108295])).

tff(c_108303,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_108300])).

tff(c_108307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_108303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.20/28.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.26/28.85  
% 39.26/28.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.26/28.85  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 39.26/28.85  
% 39.26/28.85  %Foreground sorts:
% 39.26/28.85  
% 39.26/28.85  
% 39.26/28.85  %Background operators:
% 39.26/28.85  
% 39.26/28.85  
% 39.26/28.85  %Foreground operators:
% 39.26/28.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.26/28.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 39.26/28.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 39.26/28.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.26/28.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 39.26/28.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 39.26/28.85  tff('#skF_2', type, '#skF_2': $i).
% 39.26/28.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 39.26/28.85  tff('#skF_3', type, '#skF_3': $i).
% 39.26/28.85  tff('#skF_1', type, '#skF_1': $i).
% 39.26/28.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.26/28.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.26/28.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.26/28.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 39.26/28.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.26/28.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 39.26/28.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 39.26/28.85  
% 39.31/28.87  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 39.31/28.87  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 39.31/28.87  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 39.31/28.87  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 39.31/28.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 39.31/28.87  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 39.31/28.87  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 39.31/28.87  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 39.31/28.87  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 39.31/28.87  tff(f_55, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 39.31/28.87  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 39.31/28.87  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 39.31/28.87  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.31/28.87  tff(c_72, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 39.31/28.87  tff(c_83, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_72])).
% 39.31/28.87  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 39.31/28.87  tff(c_88, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_83, c_14])).
% 39.31/28.87  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 39.31/28.87  tff(c_44, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 39.31/28.87  tff(c_51, plain, (![A_11, B_12]: (k2_xboole_0(k4_xboole_0(A_11, B_12), A_11)=A_11)), inference(resolution, [status(thm)], [c_16, c_44])).
% 39.31/28.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.31/28.87  tff(c_114, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(k2_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.31/28.87  tff(c_132, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(resolution, [status(thm)], [c_6, c_114])).
% 39.31/28.87  tff(c_12, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 39.31/28.87  tff(c_158, plain, (![A_64, B_65, B_66]: (r1_tarski(A_64, k2_xboole_0(k2_xboole_0(A_64, B_65), B_66)))), inference(resolution, [status(thm)], [c_132, c_12])).
% 39.31/28.87  tff(c_272, plain, (![A_73, B_74, B_75]: (r1_tarski(k4_xboole_0(A_73, B_74), k2_xboole_0(A_73, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_158])).
% 39.31/28.87  tff(c_283, plain, (![B_74]: (r1_tarski(k4_xboole_0('#skF_2', B_74), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_272])).
% 39.31/28.87  tff(c_26, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 39.31/28.87  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.31/28.87  tff(c_30, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 39.31/28.87  tff(c_1539, plain, (![A_171, B_172]: (r1_tarski(k1_tops_1(A_171, B_172), B_172) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_76])).
% 39.31/28.87  tff(c_1992, plain, (![A_184, A_185]: (r1_tarski(k1_tops_1(A_184, A_185), A_185) | ~l1_pre_topc(A_184) | ~r1_tarski(A_185, u1_struct_0(A_184)))), inference(resolution, [status(thm)], [c_26, c_1539])).
% 39.31/28.87  tff(c_4960, plain, (![A_328, A_329]: (k2_xboole_0(k1_tops_1(A_328, A_329), A_329)=A_329 | ~l1_pre_topc(A_328) | ~r1_tarski(A_329, u1_struct_0(A_328)))), inference(resolution, [status(thm)], [c_1992, c_14])).
% 39.31/28.87  tff(c_5014, plain, (![B_74]: (k2_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', B_74)), k4_xboole_0('#skF_2', B_74))=k4_xboole_0('#skF_2', B_74) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_283, c_4960])).
% 39.31/28.87  tff(c_95568, plain, (![B_2046]: (k2_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', B_2046)), k4_xboole_0('#skF_2', B_2046))=k4_xboole_0('#skF_2', B_2046))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5014])).
% 39.31/28.87  tff(c_131, plain, (![A_59, B_61]: (r1_tarski(A_59, k2_xboole_0(A_59, B_61)))), inference(resolution, [status(thm)], [c_6, c_114])).
% 39.31/28.87  tff(c_95858, plain, (![B_2047]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', B_2047)), k4_xboole_0('#skF_2', B_2047)))), inference(superposition, [status(thm), theory('equality')], [c_95568, c_131])).
% 39.31/28.87  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.31/28.87  tff(c_1546, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1539])).
% 39.31/28.87  tff(c_1553, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1546])).
% 39.31/28.87  tff(c_97, plain, (![A_51, C_52, B_53]: (r1_xboole_0(A_51, C_52) | ~r1_tarski(A_51, k4_xboole_0(B_53, C_52)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 39.31/28.87  tff(c_107, plain, (![B_53, C_52]: (r1_xboole_0(k4_xboole_0(B_53, C_52), C_52))), inference(resolution, [status(thm)], [c_6, c_97])).
% 39.31/28.87  tff(c_1223, plain, (![A_148, C_149, B_150, D_151]: (r1_xboole_0(A_148, C_149) | ~r1_xboole_0(B_150, D_151) | ~r1_tarski(C_149, D_151) | ~r1_tarski(A_148, B_150))), inference(cnfTransformation, [status(thm)], [f_55])).
% 39.31/28.87  tff(c_3999, plain, (![A_282, C_283, C_284, B_285]: (r1_xboole_0(A_282, C_283) | ~r1_tarski(C_283, C_284) | ~r1_tarski(A_282, k4_xboole_0(B_285, C_284)))), inference(resolution, [status(thm)], [c_107, c_1223])).
% 39.31/28.87  tff(c_4155, plain, (![A_282, B_285]: (r1_xboole_0(A_282, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(A_282, k4_xboole_0(B_285, '#skF_3')))), inference(resolution, [status(thm)], [c_1553, c_3999])).
% 39.31/28.87  tff(c_96122, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_95858, c_4155])).
% 39.31/28.87  tff(c_20, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k4_xboole_0(B_18, C_19)) | ~r1_xboole_0(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 39.31/28.87  tff(c_1544, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1539])).
% 39.31/28.87  tff(c_1550, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1544])).
% 39.31/28.87  tff(c_1563, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_1550, c_14])).
% 39.31/28.87  tff(c_152, plain, (![A_6, B_7, B_63]: (r1_tarski(A_6, k2_xboole_0(k2_xboole_0(A_6, B_7), B_63)))), inference(resolution, [status(thm)], [c_132, c_12])).
% 39.31/28.87  tff(c_1648, plain, (![B_173]: (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', B_173)))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_152])).
% 39.31/28.87  tff(c_577, plain, (![A_102, B_103, C_104]: (k7_subset_1(A_102, B_103, C_104)=k4_xboole_0(B_103, C_104) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 39.31/28.87  tff(c_584, plain, (![B_24, A_23, C_104]: (k7_subset_1(B_24, A_23, C_104)=k4_xboole_0(A_23, C_104) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_26, c_577])).
% 39.31/28.87  tff(c_86719, plain, (![B_1932, C_1933]: (k7_subset_1(k2_xboole_0('#skF_2', B_1932), k1_tops_1('#skF_1', '#skF_2'), C_1933)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_1933))), inference(resolution, [status(thm)], [c_1648, c_584])).
% 39.31/28.87  tff(c_86745, plain, (![C_1933]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_1933)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_1933))), inference(superposition, [status(thm), theory('equality')], [c_88, c_86719])).
% 39.31/28.87  tff(c_585, plain, (![C_104]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_104)=k4_xboole_0('#skF_2', C_104))), inference(resolution, [status(thm)], [c_36, c_577])).
% 39.31/28.87  tff(c_32, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 39.31/28.87  tff(c_587, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_585, c_32])).
% 39.31/28.87  tff(c_87040, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86745, c_587])).
% 39.31/28.87  tff(c_87975, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_87040])).
% 39.31/28.87  tff(c_108286, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96122, c_87975])).
% 39.31/28.87  tff(c_108295, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_108286])).
% 39.31/28.87  tff(c_108300, plain, (~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_16, c_108295])).
% 39.31/28.87  tff(c_108303, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_108300])).
% 39.31/28.87  tff(c_108307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_108303])).
% 39.31/28.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.31/28.87  
% 39.31/28.87  Inference rules
% 39.31/28.87  ----------------------
% 39.31/28.87  #Ref     : 0
% 39.31/28.87  #Sup     : 28563
% 39.31/28.87  #Fact    : 0
% 39.31/28.87  #Define  : 0
% 39.31/28.87  #Split   : 40
% 39.31/28.87  #Chain   : 0
% 39.31/28.87  #Close   : 0
% 39.31/28.87  
% 39.31/28.87  Ordering : KBO
% 39.31/28.87  
% 39.31/28.87  Simplification rules
% 39.31/28.87  ----------------------
% 39.31/28.87  #Subsume      : 8059
% 39.31/28.87  #Demod        : 8754
% 39.31/28.87  #Tautology    : 5623
% 39.31/28.87  #SimpNegUnit  : 65
% 39.31/28.87  #BackRed      : 46
% 39.31/28.87  
% 39.31/28.87  #Partial instantiations: 0
% 39.31/28.87  #Strategies tried      : 1
% 39.31/28.87  
% 39.31/28.87  Timing (in seconds)
% 39.31/28.87  ----------------------
% 39.31/28.87  Preprocessing        : 0.31
% 39.31/28.87  Parsing              : 0.17
% 39.31/28.87  CNF conversion       : 0.02
% 39.31/28.87  Main loop            : 27.80
% 39.31/28.87  Inferencing          : 2.65
% 39.31/28.88  Reduction            : 14.48
% 39.31/28.88  Demodulation         : 12.39
% 39.31/28.88  BG Simplification    : 0.31
% 39.31/28.88  Subsumption          : 8.85
% 39.31/28.88  Abstraction          : 0.46
% 39.31/28.88  MUC search           : 0.00
% 39.31/28.88  Cooper               : 0.00
% 39.31/28.88  Total                : 28.14
% 39.31/28.88  Index Insertion      : 0.00
% 39.31/28.88  Index Deletion       : 0.00
% 39.31/28.88  Index Matching       : 0.00
% 39.31/28.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
