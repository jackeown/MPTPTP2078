%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:45 EST 2020

% Result     : Theorem 38.59s
% Output     : CNFRefutation 38.59s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 236 expanded)
%              Number of leaves         :   27 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 573 expanded)
%              Number of equality atoms :   20 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_setfam_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v2_tops_2(C,A) )
                 => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_26,plain,(
    ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k7_setfam_1(A_13,B_14),k1_zfmisc_1(k1_zfmisc_1(A_13)))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_324,plain,(
    ! [A_55,B_56] :
      ( k7_setfam_1(A_55,k7_setfam_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_334,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_324])).

tff(c_1720,plain,(
    ! [B_97,A_98,C_99] :
      ( r1_tarski(B_97,k7_setfam_1(A_98,C_99))
      | ~ r1_tarski(k7_setfam_1(A_98,B_97),C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k1_zfmisc_1(A_98)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k1_zfmisc_1(A_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1722,plain,(
    ! [C_99] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),C_99))
      | ~ r1_tarski('#skF_2',C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_1720])).

tff(c_1876,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_1722])).

tff(c_1967,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_12,c_1876])).

tff(c_1971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1967])).

tff(c_1973,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_1722])).

tff(c_1218,plain,(
    ! [B_79,A_80] :
      ( v2_tops_2(B_79,A_80)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_80),B_79),A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80))))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1222,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_1218])).

tff(c_1229,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1222])).

tff(c_1714,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_1229])).

tff(c_2084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_1714])).

tff(c_2086,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_1229])).

tff(c_2089,plain,(
    ! [B_110,A_111,C_112] :
      ( r1_tarski(B_110,k7_setfam_1(A_111,C_112))
      | ~ r1_tarski(k7_setfam_1(A_111,B_110),C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k1_zfmisc_1(A_111)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2091,plain,(
    ! [C_112] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),C_112))
      | ~ r1_tarski('#skF_2',C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_2089])).

tff(c_2383,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_2091])).

tff(c_2664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2086,c_2383])).

tff(c_7159,plain,(
    ! [C_228] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),C_228))
      | ~ r1_tarski('#skF_2',C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(splitRight,[status(thm)],[c_2091])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125719,plain,(
    ! [C_780] :
      ( k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),C_780)) = k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')
      | ~ r1_tarski('#skF_2',C_780)
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_7159,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_86,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_568,plain,(
    ! [B_65,A_66] : k3_xboole_0(k3_xboole_0(B_65,A_66),A_66) = k3_xboole_0(B_65,A_66) ),
    inference(resolution,[status(thm)],[c_53,c_86])).

tff(c_1018,plain,(
    ! [A_76,B_77] : k3_xboole_0(k3_xboole_0(A_76,B_77),A_76) = k3_xboole_0(B_77,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_568])).

tff(c_1079,plain,(
    ! [A_76,B_77] : k3_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k3_xboole_0(B_77,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_2])).

tff(c_333,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_324])).

tff(c_1241,plain,(
    ! [B_81,A_82,C_83] :
      ( r1_tarski(B_81,k7_setfam_1(A_82,C_83))
      | ~ r1_tarski(k7_setfam_1(A_82,B_81),C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_zfmisc_1(A_82)))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1245,plain,(
    ! [C_83] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k7_setfam_1(u1_struct_0('#skF_1'),C_83))
      | ~ r1_tarski('#skF_3',C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_1241])).

tff(c_1249,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_1245])).

tff(c_1432,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_12,c_1249])).

tff(c_1436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1432])).

tff(c_1438,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_1245])).

tff(c_1224,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v1_tops_2('#skF_3','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_1218])).

tff(c_1231,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v1_tops_2('#skF_3','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1224])).

tff(c_1235,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_1231])).

tff(c_1709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_1235])).

tff(c_1711,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_1231])).

tff(c_2093,plain,(
    ! [C_112] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k7_setfam_1(u1_struct_0('#skF_1'),C_112))
      | ~ r1_tarski('#skF_3',C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_2089])).

tff(c_2097,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_2093])).

tff(c_2379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_2097])).

tff(c_2381,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_28,plain,(
    v2_tops_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_863,plain,(
    ! [A_72,B_73] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_72),B_73),A_72)
      | ~ v2_tops_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_72))))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_877,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v2_tops_2('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_863])).

tff(c_893,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_877])).

tff(c_165,plain,(
    ! [A_49,B_50] : k3_xboole_0(k3_xboole_0(A_49,B_50),A_49) = k3_xboole_0(A_49,B_50) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_208,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_553,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k7_setfam_1(A_63,B_64),k1_zfmisc_1(k1_zfmisc_1(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( k9_subset_1(A_10,B_11,C_12) = k3_xboole_0(B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3627,plain,(
    ! [A_148,B_149,B_150] :
      ( k9_subset_1(k1_zfmisc_1(A_148),B_149,k7_setfam_1(A_148,B_150)) = k3_xboole_0(B_149,k7_setfam_1(A_148,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_zfmisc_1(A_148))) ) ),
    inference(resolution,[status(thm)],[c_553,c_10])).

tff(c_3990,plain,(
    ! [B_158] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_158,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_xboole_0(B_158,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_3627])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k9_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3996,plain,(
    ! [B_158] :
      ( m1_subset_1(k3_xboole_0(B_158,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3990,c_8])).

tff(c_6129,plain,(
    ! [B_208] : m1_subset_1(k3_xboole_0(B_208,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2381,c_3996])).

tff(c_6261,plain,(
    ! [A_210] : m1_subset_1(k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),A_210),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6129])).

tff(c_2930,plain,(
    ! [B_137,A_138,C_139] :
      ( v1_tops_2(B_137,A_138)
      | ~ v1_tops_2(C_139,A_138)
      | ~ r1_tarski(B_137,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138))))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138))))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2947,plain,(
    ! [A_3,B_4,A_138] :
      ( v1_tops_2(k3_xboole_0(A_3,B_4),A_138)
      | ~ v1_tops_2(A_3,A_138)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138))))
      | ~ m1_subset_1(k3_xboole_0(A_3,B_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138))))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_4,c_2930])).

tff(c_6264,plain,(
    ! [A_210] :
      ( v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),A_210),'#skF_1')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6261,c_2947])).

tff(c_6377,plain,(
    ! [A_212] : v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3'),A_212),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2381,c_893,c_6264])).

tff(c_6381,plain,(
    ! [B_77] : v1_tops_2(k3_xboole_0(B_77,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_6377])).

tff(c_125815,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125719,c_6381])).

tff(c_126017,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_125815])).

tff(c_20,plain,(
    ! [B_23,A_21] :
      ( v2_tops_2(B_23,A_21)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_21),B_23),A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21))))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_126047,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_126017,c_20])).

tff(c_126050,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_126047])).

tff(c_126052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_126050])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.59/28.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.59/28.70  
% 38.59/28.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.59/28.70  %$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_setfam_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 38.59/28.70  
% 38.59/28.70  %Foreground sorts:
% 38.59/28.70  
% 38.59/28.70  
% 38.59/28.70  %Background operators:
% 38.59/28.70  
% 38.59/28.70  
% 38.59/28.70  %Foreground operators:
% 38.59/28.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.59/28.70  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 38.59/28.70  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 38.59/28.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 38.59/28.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 38.59/28.70  tff('#skF_2', type, '#skF_2': $i).
% 38.59/28.70  tff('#skF_3', type, '#skF_3': $i).
% 38.59/28.70  tff('#skF_1', type, '#skF_1': $i).
% 38.59/28.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 38.59/28.70  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 38.59/28.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.59/28.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.59/28.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.59/28.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 38.59/28.70  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 38.59/28.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 38.59/28.70  
% 38.59/28.72  tff(f_96, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 38.59/28.72  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 38.59/28.72  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 38.59/28.72  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_setfam_1)).
% 38.59/28.72  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tops_2)).
% 38.59/28.72  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.59/28.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 38.59/28.72  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 38.59/28.72  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 38.59/28.72  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 38.59/28.72  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 38.59/28.72  tff(c_26, plain, (~v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 38.59/28.72  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 38.59/28.72  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 38.59/28.72  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 38.59/28.72  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 38.59/28.72  tff(c_12, plain, (![A_13, B_14]: (m1_subset_1(k7_setfam_1(A_13, B_14), k1_zfmisc_1(k1_zfmisc_1(A_13))) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 38.59/28.72  tff(c_324, plain, (![A_55, B_56]: (k7_setfam_1(A_55, k7_setfam_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 38.59/28.72  tff(c_334, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_324])).
% 38.59/28.72  tff(c_1720, plain, (![B_97, A_98, C_99]: (r1_tarski(B_97, k7_setfam_1(A_98, C_99)) | ~r1_tarski(k7_setfam_1(A_98, B_97), C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k1_zfmisc_1(A_98))) | ~m1_subset_1(B_97, k1_zfmisc_1(k1_zfmisc_1(A_98))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 38.59/28.72  tff(c_1722, plain, (![C_99]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), C_99)) | ~r1_tarski('#skF_2', C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_334, c_1720])).
% 38.59/28.72  tff(c_1876, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_1722])).
% 38.59/28.72  tff(c_1967, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_12, c_1876])).
% 38.59/28.72  tff(c_1971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1967])).
% 38.59/28.72  tff(c_1973, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_1722])).
% 38.59/28.72  tff(c_1218, plain, (![B_79, A_80]: (v2_tops_2(B_79, A_80) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_80), B_79), A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80)))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.59/28.72  tff(c_1222, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_334, c_1218])).
% 38.59/28.72  tff(c_1229, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1222])).
% 38.59/28.72  tff(c_1714, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_1229])).
% 38.59/28.72  tff(c_2084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1973, c_1714])).
% 38.59/28.72  tff(c_2086, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_1229])).
% 38.59/28.72  tff(c_2089, plain, (![B_110, A_111, C_112]: (r1_tarski(B_110, k7_setfam_1(A_111, C_112)) | ~r1_tarski(k7_setfam_1(A_111, B_110), C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k1_zfmisc_1(A_111))) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 38.59/28.72  tff(c_2091, plain, (![C_112]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), C_112)) | ~r1_tarski('#skF_2', C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_334, c_2089])).
% 38.59/28.72  tff(c_2383, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_2091])).
% 38.59/28.72  tff(c_2664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2086, c_2383])).
% 38.59/28.72  tff(c_7159, plain, (![C_228]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), C_228)) | ~r1_tarski('#skF_2', C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(splitRight, [status(thm)], [c_2091])).
% 38.59/28.72  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 38.59/28.72  tff(c_125719, plain, (![C_780]: (k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), C_780))=k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2') | ~r1_tarski('#skF_2', C_780) | ~m1_subset_1(C_780, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_7159, c_6])).
% 38.59/28.72  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 38.59/28.72  tff(c_38, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 38.59/28.72  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 38.59/28.72  tff(c_53, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_38, c_4])).
% 38.59/28.72  tff(c_86, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 38.59/28.72  tff(c_568, plain, (![B_65, A_66]: (k3_xboole_0(k3_xboole_0(B_65, A_66), A_66)=k3_xboole_0(B_65, A_66))), inference(resolution, [status(thm)], [c_53, c_86])).
% 38.59/28.72  tff(c_1018, plain, (![A_76, B_77]: (k3_xboole_0(k3_xboole_0(A_76, B_77), A_76)=k3_xboole_0(B_77, A_76))), inference(superposition, [status(thm), theory('equality')], [c_2, c_568])).
% 38.59/28.72  tff(c_1079, plain, (![A_76, B_77]: (k3_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k3_xboole_0(B_77, A_76))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_2])).
% 38.59/28.72  tff(c_333, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_32, c_324])).
% 38.59/28.72  tff(c_1241, plain, (![B_81, A_82, C_83]: (r1_tarski(B_81, k7_setfam_1(A_82, C_83)) | ~r1_tarski(k7_setfam_1(A_82, B_81), C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k1_zfmisc_1(A_82))) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 38.59/28.72  tff(c_1245, plain, (![C_83]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k7_setfam_1(u1_struct_0('#skF_1'), C_83)) | ~r1_tarski('#skF_3', C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_333, c_1241])).
% 38.59/28.72  tff(c_1249, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_1245])).
% 38.59/28.72  tff(c_1432, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_12, c_1249])).
% 38.59/28.72  tff(c_1436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1432])).
% 38.59/28.72  tff(c_1438, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_1245])).
% 38.59/28.72  tff(c_1224, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v1_tops_2('#skF_3', '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_333, c_1218])).
% 38.59/28.72  tff(c_1231, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v1_tops_2('#skF_3', '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1224])).
% 38.59/28.72  tff(c_1235, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_1231])).
% 38.59/28.72  tff(c_1709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1438, c_1235])).
% 38.59/28.72  tff(c_1711, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_1231])).
% 38.59/28.72  tff(c_2093, plain, (![C_112]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k7_setfam_1(u1_struct_0('#skF_1'), C_112)) | ~r1_tarski('#skF_3', C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_333, c_2089])).
% 38.59/28.72  tff(c_2097, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_2093])).
% 38.59/28.72  tff(c_2379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1711, c_2097])).
% 38.59/28.72  tff(c_2381, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_2093])).
% 38.59/28.72  tff(c_28, plain, (v2_tops_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 38.59/28.72  tff(c_863, plain, (![A_72, B_73]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_72), B_73), A_72) | ~v2_tops_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_72)))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.59/28.72  tff(c_877, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v2_tops_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_863])).
% 38.59/28.72  tff(c_893, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_877])).
% 38.59/28.72  tff(c_165, plain, (![A_49, B_50]: (k3_xboole_0(k3_xboole_0(A_49, B_50), A_49)=k3_xboole_0(A_49, B_50))), inference(resolution, [status(thm)], [c_4, c_86])).
% 38.59/28.72  tff(c_208, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_165])).
% 38.59/28.72  tff(c_553, plain, (![A_63, B_64]: (m1_subset_1(k7_setfam_1(A_63, B_64), k1_zfmisc_1(k1_zfmisc_1(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 38.59/28.72  tff(c_10, plain, (![A_10, B_11, C_12]: (k9_subset_1(A_10, B_11, C_12)=k3_xboole_0(B_11, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 38.59/28.72  tff(c_3627, plain, (![A_148, B_149, B_150]: (k9_subset_1(k1_zfmisc_1(A_148), B_149, k7_setfam_1(A_148, B_150))=k3_xboole_0(B_149, k7_setfam_1(A_148, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(k1_zfmisc_1(A_148))))), inference(resolution, [status(thm)], [c_553, c_10])).
% 38.59/28.72  tff(c_3990, plain, (![B_158]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_158, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_xboole_0(B_158, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3')))), inference(resolution, [status(thm)], [c_32, c_3627])).
% 38.59/28.72  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k9_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 38.59/28.72  tff(c_3996, plain, (![B_158]: (m1_subset_1(k3_xboole_0(B_158, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_3990, c_8])).
% 38.59/28.72  tff(c_6129, plain, (![B_208]: (m1_subset_1(k3_xboole_0(B_208, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_2381, c_3996])).
% 38.59/28.72  tff(c_6261, plain, (![A_210]: (m1_subset_1(k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), A_210), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_208, c_6129])).
% 38.59/28.72  tff(c_2930, plain, (![B_137, A_138, C_139]: (v1_tops_2(B_137, A_138) | ~v1_tops_2(C_139, A_138) | ~r1_tarski(B_137, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138)))) | ~m1_subset_1(B_137, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138)))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_81])).
% 38.59/28.72  tff(c_2947, plain, (![A_3, B_4, A_138]: (v1_tops_2(k3_xboole_0(A_3, B_4), A_138) | ~v1_tops_2(A_3, A_138) | ~m1_subset_1(A_3, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138)))) | ~m1_subset_1(k3_xboole_0(A_3, B_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138)))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_4, c_2930])).
% 38.59/28.72  tff(c_6264, plain, (![A_210]: (v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), A_210), '#skF_1') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_6261, c_2947])).
% 38.59/28.72  tff(c_6377, plain, (![A_212]: (v1_tops_2(k3_xboole_0(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3'), A_212), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2381, c_893, c_6264])).
% 38.59/28.72  tff(c_6381, plain, (![B_77]: (v1_tops_2(k3_xboole_0(B_77, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1079, c_6377])).
% 38.59/28.72  tff(c_125815, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_125719, c_6381])).
% 38.59/28.72  tff(c_126017, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_125815])).
% 38.59/28.72  tff(c_20, plain, (![B_23, A_21]: (v2_tops_2(B_23, A_21) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_21), B_23), A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21)))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 38.59/28.72  tff(c_126047, plain, (v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_126017, c_20])).
% 38.59/28.72  tff(c_126050, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_126047])).
% 38.59/28.72  tff(c_126052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_126050])).
% 38.59/28.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 38.59/28.72  
% 38.59/28.72  Inference rules
% 38.59/28.72  ----------------------
% 38.59/28.72  #Ref     : 0
% 38.59/28.72  #Sup     : 27259
% 38.59/28.72  #Fact    : 0
% 38.59/28.72  #Define  : 0
% 38.59/28.72  #Split   : 21
% 38.59/28.72  #Chain   : 0
% 38.59/28.72  #Close   : 0
% 38.59/28.72  
% 38.59/28.72  Ordering : KBO
% 38.59/28.72  
% 38.59/28.72  Simplification rules
% 38.59/28.72  ----------------------
% 38.59/28.72  #Subsume      : 5861
% 38.59/28.72  #Demod        : 36573
% 38.59/28.72  #Tautology    : 8696
% 38.59/28.72  #SimpNegUnit  : 101
% 38.59/28.72  #BackRed      : 4
% 38.59/28.72  
% 38.59/28.72  #Partial instantiations: 0
% 38.59/28.72  #Strategies tried      : 1
% 38.59/28.72  
% 38.59/28.72  Timing (in seconds)
% 38.59/28.72  ----------------------
% 38.79/28.73  Preprocessing        : 0.31
% 38.79/28.73  Parsing              : 0.16
% 38.79/28.73  CNF conversion       : 0.02
% 38.79/28.73  Main loop            : 27.64
% 38.79/28.73  Inferencing          : 2.43
% 38.79/28.73  Reduction            : 19.21
% 38.79/28.73  Demodulation         : 17.96
% 38.79/28.73  BG Simplification    : 0.30
% 38.79/28.73  Subsumption          : 4.98
% 38.79/28.73  Abstraction          : 0.57
% 38.79/28.73  MUC search           : 0.00
% 38.79/28.73  Cooper               : 0.00
% 38.79/28.73  Total                : 27.99
% 38.79/28.73  Index Insertion      : 0.00
% 38.79/28.73  Index Deletion       : 0.00
% 38.79/28.73  Index Matching       : 0.00
% 38.79/28.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
