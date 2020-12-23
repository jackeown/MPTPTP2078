%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:53 EST 2020

% Result     : Theorem 20.17s
% Output     : CNFRefutation 20.17s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 205 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 415 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_60,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2814,plain,(
    ! [A_228,C_229,B_230] :
      ( r1_tarski(k2_pre_topc(A_228,C_229),B_230)
      | ~ r1_tarski(C_229,B_230)
      | ~ v4_pre_topc(B_230,A_228)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2824,plain,(
    ! [B_230] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),B_230)
      | ~ r1_tarski('#skF_3',B_230)
      | ~ v4_pre_topc(B_230,'#skF_2')
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_2814])).

tff(c_14612,plain,(
    ! [B_413] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),B_413)
      | ~ r1_tarski('#skF_3',B_413)
      | ~ v4_pre_topc(B_413,'#skF_2')
      | ~ m1_subset_1(B_413,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2824])).

tff(c_14635,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_14612])).

tff(c_14647,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12,c_14635])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14670,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14647,c_8])).

tff(c_47223,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14670])).

tff(c_2742,plain,(
    ! [A_224,B_225] :
      ( k4_subset_1(u1_struct_0(A_224),B_225,k2_tops_1(A_224,B_225)) = k2_pre_topc(A_224,B_225)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2752,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2742])).

tff(c_2758,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2752])).

tff(c_40,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2520,plain,(
    ! [A_220,B_221] :
      ( k2_tops_1(A_220,k3_subset_1(u1_struct_0(A_220),B_221)) = k2_tops_1(A_220,B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2530,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_2520])).

tff(c_2536,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2530])).

tff(c_1979,plain,(
    ! [A_195,B_196] :
      ( m1_subset_1(k2_tops_1(A_195,B_196),k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7714,plain,(
    ! [A_327,B_328] :
      ( r1_tarski(k2_tops_1(A_327,B_328),u1_struct_0(A_327))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327) ) ),
    inference(resolution,[status(thm)],[c_1979,c_46])).

tff(c_7733,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2536,c_7714])).

tff(c_7743,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_7733])).

tff(c_59114,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7743])).

tff(c_59117,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_40,c_59114])).

tff(c_59124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_59117])).

tff(c_59125,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7743])).

tff(c_48,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(A_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2167,plain,(
    ! [A_210,B_211,C_212] :
      ( k4_subset_1(A_210,B_211,C_212) = k2_xboole_0(B_211,C_212)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(A_210))
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11784,plain,(
    ! [B_377,B_378,A_379] :
      ( k4_subset_1(B_377,B_378,A_379) = k2_xboole_0(B_378,A_379)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(B_377))
      | ~ r1_tarski(A_379,B_377) ) ),
    inference(resolution,[status(thm)],[c_48,c_2167])).

tff(c_11803,plain,(
    ! [A_379] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',A_379) = k2_xboole_0('#skF_3',A_379)
      | ~ r1_tarski(A_379,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_64,c_11784])).

tff(c_59140,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_59125,c_11803])).

tff(c_59165,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2758,c_59140])).

tff(c_32,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_59877,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_59165,c_32])).

tff(c_59891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47223,c_59877])).

tff(c_59892,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14670])).

tff(c_59918,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59892,c_2758])).

tff(c_77036,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7743])).

tff(c_77039,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_40,c_77036])).

tff(c_77046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_77039])).

tff(c_77047,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_7743])).

tff(c_77062,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_77047,c_11803])).

tff(c_77087,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59918,c_77062])).

tff(c_34,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_247,plain,(
    ! [B_91,A_92] : k3_tarski(k2_tarski(B_91,A_92)) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_145])).

tff(c_36,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_270,plain,(
    ! [B_93,A_94] : k2_xboole_0(B_93,A_94) = k2_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_36])).

tff(c_285,plain,(
    ! [A_94,B_93] : r1_tarski(A_94,k2_xboole_0(B_93,A_94)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_32])).

tff(c_77276,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_77087,c_285])).

tff(c_77314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_77276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.17/12.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.17/12.44  
% 20.17/12.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.17/12.44  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 20.17/12.44  
% 20.17/12.44  %Foreground sorts:
% 20.17/12.44  
% 20.17/12.44  
% 20.17/12.44  %Background operators:
% 20.17/12.44  
% 20.17/12.44  
% 20.17/12.44  %Foreground operators:
% 20.17/12.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.17/12.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.17/12.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.17/12.44  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 20.17/12.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.17/12.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.17/12.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.17/12.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.17/12.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.17/12.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 20.17/12.44  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 20.17/12.44  tff('#skF_2', type, '#skF_2': $i).
% 20.17/12.44  tff('#skF_3', type, '#skF_3': $i).
% 20.17/12.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.17/12.44  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 20.17/12.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.17/12.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.17/12.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.17/12.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.17/12.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.17/12.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.17/12.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.17/12.44  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 20.17/12.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.17/12.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 20.17/12.44  
% 20.17/12.45  tff(f_139, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 20.17/12.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.17/12.45  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_1)).
% 20.17/12.45  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 20.17/12.45  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 20.17/12.45  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 20.17/12.45  tff(f_101, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 20.17/12.45  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 20.17/12.45  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 20.17/12.45  tff(f_66, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.17/12.45  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 20.17/12.45  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 20.17/12.45  tff(c_60, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 20.17/12.45  tff(c_62, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 20.17/12.45  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.17/12.45  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 20.17/12.45  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 20.17/12.45  tff(c_2814, plain, (![A_228, C_229, B_230]: (r1_tarski(k2_pre_topc(A_228, C_229), B_230) | ~r1_tarski(C_229, B_230) | ~v4_pre_topc(B_230, A_228) | ~m1_subset_1(C_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_115])).
% 20.17/12.45  tff(c_2824, plain, (![B_230]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), B_230) | ~r1_tarski('#skF_3', B_230) | ~v4_pre_topc(B_230, '#skF_2') | ~m1_subset_1(B_230, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_2814])).
% 20.17/12.45  tff(c_14612, plain, (![B_413]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), B_413) | ~r1_tarski('#skF_3', B_413) | ~v4_pre_topc(B_413, '#skF_2') | ~m1_subset_1(B_413, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2824])).
% 20.17/12.45  tff(c_14635, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_14612])).
% 20.17/12.45  tff(c_14647, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12, c_14635])).
% 20.17/12.45  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.17/12.45  tff(c_14670, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_14647, c_8])).
% 20.17/12.45  tff(c_47223, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_14670])).
% 20.17/12.45  tff(c_2742, plain, (![A_224, B_225]: (k4_subset_1(u1_struct_0(A_224), B_225, k2_tops_1(A_224, B_225))=k2_pre_topc(A_224, B_225) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_129])).
% 20.17/12.45  tff(c_2752, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2742])).
% 20.17/12.45  tff(c_2758, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2752])).
% 20.17/12.45  tff(c_40, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 20.17/12.45  tff(c_2520, plain, (![A_220, B_221]: (k2_tops_1(A_220, k3_subset_1(u1_struct_0(A_220), B_221))=k2_tops_1(A_220, B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_122])).
% 20.17/12.45  tff(c_2530, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_2520])).
% 20.17/12.45  tff(c_2536, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2530])).
% 20.17/12.45  tff(c_1979, plain, (![A_195, B_196]: (m1_subset_1(k2_tops_1(A_195, B_196), k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.17/12.45  tff(c_46, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 20.17/12.45  tff(c_7714, plain, (![A_327, B_328]: (r1_tarski(k2_tops_1(A_327, B_328), u1_struct_0(A_327)) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0(A_327))) | ~l1_pre_topc(A_327))), inference(resolution, [status(thm)], [c_1979, c_46])).
% 20.17/12.45  tff(c_7733, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2536, c_7714])).
% 20.17/12.45  tff(c_7743, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_7733])).
% 20.17/12.45  tff(c_59114, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_7743])).
% 20.17/12.45  tff(c_59117, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_59114])).
% 20.17/12.45  tff(c_59124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_59117])).
% 20.17/12.45  tff(c_59125, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_7743])).
% 20.17/12.45  tff(c_48, plain, (![A_42, B_43]: (m1_subset_1(A_42, k1_zfmisc_1(B_43)) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_90])).
% 20.17/12.45  tff(c_2167, plain, (![A_210, B_211, C_212]: (k4_subset_1(A_210, B_211, C_212)=k2_xboole_0(B_211, C_212) | ~m1_subset_1(C_212, k1_zfmisc_1(A_210)) | ~m1_subset_1(B_211, k1_zfmisc_1(A_210)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 20.17/12.45  tff(c_11784, plain, (![B_377, B_378, A_379]: (k4_subset_1(B_377, B_378, A_379)=k2_xboole_0(B_378, A_379) | ~m1_subset_1(B_378, k1_zfmisc_1(B_377)) | ~r1_tarski(A_379, B_377))), inference(resolution, [status(thm)], [c_48, c_2167])).
% 20.17/12.45  tff(c_11803, plain, (![A_379]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', A_379)=k2_xboole_0('#skF_3', A_379) | ~r1_tarski(A_379, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_64, c_11784])).
% 20.17/12.45  tff(c_59140, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_59125, c_11803])).
% 20.17/12.45  tff(c_59165, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2758, c_59140])).
% 20.17/12.45  tff(c_32, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.17/12.45  tff(c_59877, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_59165, c_32])).
% 20.17/12.45  tff(c_59891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47223, c_59877])).
% 20.17/12.45  tff(c_59892, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_14670])).
% 20.17/12.45  tff(c_59918, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59892, c_2758])).
% 20.17/12.45  tff(c_77036, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_7743])).
% 20.17/12.45  tff(c_77039, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_77036])).
% 20.17/12.45  tff(c_77046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_77039])).
% 20.17/12.45  tff(c_77047, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_7743])).
% 20.17/12.45  tff(c_77062, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_77047, c_11803])).
% 20.17/12.45  tff(c_77087, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59918, c_77062])).
% 20.17/12.45  tff(c_34, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 20.17/12.45  tff(c_145, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.17/12.45  tff(c_247, plain, (![B_91, A_92]: (k3_tarski(k2_tarski(B_91, A_92))=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_34, c_145])).
% 20.17/12.45  tff(c_36, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 20.17/12.45  tff(c_270, plain, (![B_93, A_94]: (k2_xboole_0(B_93, A_94)=k2_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_247, c_36])).
% 20.17/12.45  tff(c_285, plain, (![A_94, B_93]: (r1_tarski(A_94, k2_xboole_0(B_93, A_94)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_32])).
% 20.17/12.45  tff(c_77276, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77087, c_285])).
% 20.17/12.45  tff(c_77314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_77276])).
% 20.17/12.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.17/12.45  
% 20.17/12.45  Inference rules
% 20.17/12.45  ----------------------
% 20.17/12.45  #Ref     : 0
% 20.17/12.45  #Sup     : 18697
% 20.17/12.45  #Fact    : 0
% 20.17/12.45  #Define  : 0
% 20.17/12.45  #Split   : 7
% 20.17/12.45  #Chain   : 0
% 20.17/12.45  #Close   : 0
% 20.17/12.45  
% 20.17/12.45  Ordering : KBO
% 20.17/12.45  
% 20.17/12.45  Simplification rules
% 20.17/12.45  ----------------------
% 20.17/12.45  #Subsume      : 1283
% 20.17/12.45  #Demod        : 19248
% 20.17/12.45  #Tautology    : 10404
% 20.17/12.45  #SimpNegUnit  : 2
% 20.17/12.45  #BackRed      : 36
% 20.17/12.45  
% 20.17/12.45  #Partial instantiations: 0
% 20.17/12.45  #Strategies tried      : 1
% 20.17/12.45  
% 20.17/12.45  Timing (in seconds)
% 20.17/12.45  ----------------------
% 20.17/12.46  Preprocessing        : 0.31
% 20.17/12.46  Parsing              : 0.16
% 20.17/12.46  CNF conversion       : 0.02
% 20.17/12.46  Main loop            : 11.27
% 20.17/12.46  Inferencing          : 1.35
% 20.17/12.46  Reduction            : 6.69
% 20.17/12.46  Demodulation         : 6.04
% 20.17/12.46  BG Simplification    : 0.15
% 20.17/12.46  Subsumption          : 2.60
% 20.17/12.46  Abstraction          : 0.26
% 20.17/12.46  MUC search           : 0.00
% 20.17/12.46  Cooper               : 0.00
% 20.17/12.46  Total                : 11.62
% 20.17/12.46  Index Insertion      : 0.00
% 20.17/12.46  Index Deletion       : 0.00
% 20.17/12.46  Index Matching       : 0.00
% 20.17/12.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
