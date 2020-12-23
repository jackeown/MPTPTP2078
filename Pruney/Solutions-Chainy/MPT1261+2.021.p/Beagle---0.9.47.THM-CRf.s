%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 11.95s
% Output     : CNFRefutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 156 expanded)
%              Number of leaves         :   45 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 302 expanded)
%              Number of equality atoms :   57 (  95 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

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

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_40,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_156,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_107,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_88,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_38261,plain,(
    ! [A_714,B_715,C_716] :
      ( k7_subset_1(A_714,B_715,C_716) = k4_xboole_0(B_715,C_716)
      | ~ m1_subset_1(B_715,k1_zfmisc_1(A_714)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38289,plain,(
    ! [C_716] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_716) = k4_xboole_0('#skF_3',C_716) ),
    inference(resolution,[status(thm)],[c_72,c_38261])).

tff(c_78,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_255,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4184,plain,(
    ! [B_264,A_265] :
      ( v4_pre_topc(B_264,A_265)
      | k2_pre_topc(A_265,B_264) != B_264
      | ~ v2_pre_topc(A_265)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4217,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_4184])).

tff(c_4230,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_4217])).

tff(c_4231,plain,(
    k2_pre_topc('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_4230])).

tff(c_4655,plain,(
    ! [A_276,B_277] :
      ( k4_subset_1(u1_struct_0(A_276),B_277,k2_tops_1(A_276,B_277)) = k2_pre_topc(A_276,B_277)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4679,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_4655])).

tff(c_4692,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4679])).

tff(c_84,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_422,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_84])).

tff(c_2590,plain,(
    ! [A_208,B_209,C_210] :
      ( k7_subset_1(A_208,B_209,C_210) = k4_xboole_0(B_209,C_210)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(A_208)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2622,plain,(
    ! [C_213] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_213) = k4_xboole_0('#skF_3',C_213) ),
    inference(resolution,[status(thm)],[c_72,c_2590])).

tff(c_2634,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_2622])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1435,plain,(
    ! [A_170,B_171,C_172] :
      ( r1_tarski(k4_xboole_0(A_170,B_171),C_172)
      | ~ r1_tarski(A_170,k2_xboole_0(B_171,C_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1455,plain,(
    ! [A_170,B_171] :
      ( k4_xboole_0(A_170,B_171) = k1_xboole_0
      | ~ r1_tarski(A_170,k2_xboole_0(B_171,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1435,c_28])).

tff(c_1488,plain,(
    ! [A_173,B_174] :
      ( k4_xboole_0(A_173,B_174) = k1_xboole_0
      | ~ r1_tarski(A_173,B_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1455])).

tff(c_1529,plain,(
    ! [A_175,B_176] : k4_xboole_0(k4_xboole_0(A_175,B_176),A_175) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1488])).

tff(c_24,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1543,plain,(
    ! [A_175,B_176] : k2_xboole_0(A_175,k4_xboole_0(A_175,B_176)) = k2_xboole_0(A_175,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_24])).

tff(c_1588,plain,(
    ! [A_175,B_176] : k2_xboole_0(A_175,k4_xboole_0(A_175,B_176)) = A_175 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1543])).

tff(c_3489,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2634,c_1588])).

tff(c_3753,plain,(
    ! [A_250,B_251] :
      ( k2_tops_1(A_250,k3_subset_1(u1_struct_0(A_250),B_251)) = k2_tops_1(A_250,B_251)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_3777,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_3753])).

tff(c_3792,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3777])).

tff(c_2242,plain,(
    ! [A_200,B_201] :
      ( k4_xboole_0(A_200,B_201) = k3_subset_1(A_200,B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(A_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2273,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2242])).

tff(c_52,plain,(
    ! [A_53,B_54] : k6_subset_1(A_53,B_54) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    ! [A_42,B_43] : m1_subset_1(k6_subset_1(A_42,B_43),k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_85,plain,(
    ! [A_42,B_43] : m1_subset_1(k4_xboole_0(A_42,B_43),k1_zfmisc_1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44])).

tff(c_2343,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2273,c_85])).

tff(c_62,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k2_tops_1(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3647,plain,(
    ! [A_246,B_247,C_248] :
      ( k4_subset_1(A_246,B_247,C_248) = k2_xboole_0(B_247,C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(A_246))
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_35535,plain,(
    ! [A_608,B_609,B_610] :
      ( k4_subset_1(u1_struct_0(A_608),B_609,k2_tops_1(A_608,B_610)) = k2_xboole_0(B_609,k2_tops_1(A_608,B_610))
      | ~ m1_subset_1(B_609,k1_zfmisc_1(u1_struct_0(A_608)))
      | ~ m1_subset_1(B_610,k1_zfmisc_1(u1_struct_0(A_608)))
      | ~ l1_pre_topc(A_608) ) ),
    inference(resolution,[status(thm)],[c_62,c_3647])).

tff(c_35570,plain,(
    ! [B_610] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_610)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_610))
      | ~ m1_subset_1(B_610,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_72,c_35535])).

tff(c_36074,plain,(
    ! [B_614] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_614)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_614))
      | ~ m1_subset_1(B_614,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_35570])).

tff(c_36093,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2343,c_36074])).

tff(c_36131,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4692,c_3489,c_3792,c_3792,c_36093])).

tff(c_36133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4231,c_36131])).

tff(c_36134,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_38317,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38289,c_36134])).

tff(c_36135,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_39050,plain,(
    ! [A_750,B_751] :
      ( k2_pre_topc(A_750,B_751) = B_751
      | ~ v4_pre_topc(B_751,A_750)
      | ~ m1_subset_1(B_751,k1_zfmisc_1(u1_struct_0(A_750)))
      | ~ l1_pre_topc(A_750) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_39080,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_39050])).

tff(c_39090,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_36135,c_39080])).

tff(c_40438,plain,(
    ! [A_797,B_798] :
      ( k7_subset_1(u1_struct_0(A_797),k2_pre_topc(A_797,B_798),k1_tops_1(A_797,B_798)) = k2_tops_1(A_797,B_798)
      | ~ m1_subset_1(B_798,k1_zfmisc_1(u1_struct_0(A_797)))
      | ~ l1_pre_topc(A_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40447,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_39090,c_40438])).

tff(c_40451,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_38289,c_40447])).

tff(c_40453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38317,c_40451])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.95/5.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.46  
% 11.95/5.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.46  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.95/5.46  
% 11.95/5.46  %Foreground sorts:
% 11.95/5.46  
% 11.95/5.46  
% 11.95/5.46  %Background operators:
% 11.95/5.46  
% 11.95/5.46  
% 11.95/5.46  %Foreground operators:
% 11.95/5.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.95/5.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.95/5.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.95/5.46  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.95/5.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.95/5.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.95/5.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.95/5.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.95/5.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.95/5.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.95/5.46  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 11.95/5.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.95/5.46  tff('#skF_2', type, '#skF_2': $i).
% 11.95/5.46  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.95/5.46  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.95/5.46  tff('#skF_3', type, '#skF_3': $i).
% 11.95/5.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.95/5.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 11.95/5.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.95/5.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.95/5.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.95/5.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.95/5.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.95/5.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.95/5.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.95/5.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.95/5.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.95/5.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.95/5.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 11.95/5.46  
% 11.95/5.48  tff(f_175, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 11.95/5.48  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.95/5.48  tff(f_128, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 11.95/5.48  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 11.95/5.48  tff(f_40, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.95/5.48  tff(f_52, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.95/5.48  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 11.95/5.48  tff(f_64, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 11.95/5.48  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.95/5.48  tff(f_156, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 11.95/5.48  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 11.95/5.48  tff(f_107, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.95/5.48  tff(f_88, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.95/5.48  tff(f_134, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 11.95/5.48  tff(f_105, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 11.95/5.48  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 11.95/5.48  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 11.95/5.48  tff(c_38261, plain, (![A_714, B_715, C_716]: (k7_subset_1(A_714, B_715, C_716)=k4_xboole_0(B_715, C_716) | ~m1_subset_1(B_715, k1_zfmisc_1(A_714)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.95/5.48  tff(c_38289, plain, (![C_716]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_716)=k4_xboole_0('#skF_3', C_716))), inference(resolution, [status(thm)], [c_72, c_38261])).
% 11.95/5.48  tff(c_78, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 11.95/5.48  tff(c_255, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_78])).
% 11.95/5.48  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 11.95/5.48  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 11.95/5.48  tff(c_4184, plain, (![B_264, A_265]: (v4_pre_topc(B_264, A_265) | k2_pre_topc(A_265, B_264)!=B_264 | ~v2_pre_topc(A_265) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.95/5.48  tff(c_4217, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3' | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_4184])).
% 11.95/5.48  tff(c_4230, plain, (v4_pre_topc('#skF_3', '#skF_2') | k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_4217])).
% 11.95/5.48  tff(c_4231, plain, (k2_pre_topc('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_255, c_4230])).
% 11.95/5.48  tff(c_4655, plain, (![A_276, B_277]: (k4_subset_1(u1_struct_0(A_276), B_277, k2_tops_1(A_276, B_277))=k2_pre_topc(A_276, B_277) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_163])).
% 11.95/5.48  tff(c_4679, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_4655])).
% 11.95/5.48  tff(c_4692, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4679])).
% 11.95/5.48  tff(c_84, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 11.95/5.48  tff(c_422, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_255, c_84])).
% 11.95/5.48  tff(c_2590, plain, (![A_208, B_209, C_210]: (k7_subset_1(A_208, B_209, C_210)=k4_xboole_0(B_209, C_210) | ~m1_subset_1(B_209, k1_zfmisc_1(A_208)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 11.95/5.48  tff(c_2622, plain, (![C_213]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_213)=k4_xboole_0('#skF_3', C_213))), inference(resolution, [status(thm)], [c_72, c_2590])).
% 11.95/5.48  tff(c_2634, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_422, c_2622])).
% 11.95/5.48  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.95/5.48  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.95/5.48  tff(c_1435, plain, (![A_170, B_171, C_172]: (r1_tarski(k4_xboole_0(A_170, B_171), C_172) | ~r1_tarski(A_170, k2_xboole_0(B_171, C_172)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.95/5.48  tff(c_28, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.95/5.48  tff(c_1455, plain, (![A_170, B_171]: (k4_xboole_0(A_170, B_171)=k1_xboole_0 | ~r1_tarski(A_170, k2_xboole_0(B_171, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1435, c_28])).
% 11.95/5.48  tff(c_1488, plain, (![A_173, B_174]: (k4_xboole_0(A_173, B_174)=k1_xboole_0 | ~r1_tarski(A_173, B_174))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1455])).
% 11.95/5.48  tff(c_1529, plain, (![A_175, B_176]: (k4_xboole_0(k4_xboole_0(A_175, B_176), A_175)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1488])).
% 11.95/5.48  tff(c_24, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.95/5.48  tff(c_1543, plain, (![A_175, B_176]: (k2_xboole_0(A_175, k4_xboole_0(A_175, B_176))=k2_xboole_0(A_175, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1529, c_24])).
% 11.95/5.48  tff(c_1588, plain, (![A_175, B_176]: (k2_xboole_0(A_175, k4_xboole_0(A_175, B_176))=A_175)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1543])).
% 11.95/5.48  tff(c_3489, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2634, c_1588])).
% 11.95/5.48  tff(c_3753, plain, (![A_250, B_251]: (k2_tops_1(A_250, k3_subset_1(u1_struct_0(A_250), B_251))=k2_tops_1(A_250, B_251) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(cnfTransformation, [status(thm)], [f_156])).
% 11.95/5.48  tff(c_3777, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_3753])).
% 11.95/5.48  tff(c_3792, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3777])).
% 11.95/5.48  tff(c_2242, plain, (![A_200, B_201]: (k4_xboole_0(A_200, B_201)=k3_subset_1(A_200, B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(A_200)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.95/5.48  tff(c_2273, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_72, c_2242])).
% 11.95/5.48  tff(c_52, plain, (![A_53, B_54]: (k6_subset_1(A_53, B_54)=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.95/5.48  tff(c_44, plain, (![A_42, B_43]: (m1_subset_1(k6_subset_1(A_42, B_43), k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.95/5.48  tff(c_85, plain, (![A_42, B_43]: (m1_subset_1(k4_xboole_0(A_42, B_43), k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44])).
% 11.95/5.48  tff(c_2343, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2273, c_85])).
% 11.95/5.48  tff(c_62, plain, (![A_63, B_64]: (m1_subset_1(k2_tops_1(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.95/5.48  tff(c_3647, plain, (![A_246, B_247, C_248]: (k4_subset_1(A_246, B_247, C_248)=k2_xboole_0(B_247, C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(A_246)) | ~m1_subset_1(B_247, k1_zfmisc_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.95/5.48  tff(c_35535, plain, (![A_608, B_609, B_610]: (k4_subset_1(u1_struct_0(A_608), B_609, k2_tops_1(A_608, B_610))=k2_xboole_0(B_609, k2_tops_1(A_608, B_610)) | ~m1_subset_1(B_609, k1_zfmisc_1(u1_struct_0(A_608))) | ~m1_subset_1(B_610, k1_zfmisc_1(u1_struct_0(A_608))) | ~l1_pre_topc(A_608))), inference(resolution, [status(thm)], [c_62, c_3647])).
% 11.95/5.48  tff(c_35570, plain, (![B_610]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_610))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_610)) | ~m1_subset_1(B_610, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_72, c_35535])).
% 11.95/5.48  tff(c_36074, plain, (![B_614]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_614))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_614)) | ~m1_subset_1(B_614, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_35570])).
% 11.95/5.48  tff(c_36093, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_2343, c_36074])).
% 11.95/5.48  tff(c_36131, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4692, c_3489, c_3792, c_3792, c_36093])).
% 11.95/5.48  tff(c_36133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4231, c_36131])).
% 11.95/5.48  tff(c_36134, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 11.95/5.48  tff(c_38317, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38289, c_36134])).
% 11.95/5.48  tff(c_36135, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_78])).
% 11.95/5.48  tff(c_39050, plain, (![A_750, B_751]: (k2_pre_topc(A_750, B_751)=B_751 | ~v4_pre_topc(B_751, A_750) | ~m1_subset_1(B_751, k1_zfmisc_1(u1_struct_0(A_750))) | ~l1_pre_topc(A_750))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.95/5.48  tff(c_39080, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_72, c_39050])).
% 11.95/5.48  tff(c_39090, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_36135, c_39080])).
% 11.95/5.48  tff(c_40438, plain, (![A_797, B_798]: (k7_subset_1(u1_struct_0(A_797), k2_pre_topc(A_797, B_798), k1_tops_1(A_797, B_798))=k2_tops_1(A_797, B_798) | ~m1_subset_1(B_798, k1_zfmisc_1(u1_struct_0(A_797))) | ~l1_pre_topc(A_797))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.95/5.48  tff(c_40447, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_39090, c_40438])).
% 11.95/5.48  tff(c_40451, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_38289, c_40447])).
% 11.95/5.48  tff(c_40453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38317, c_40451])).
% 11.95/5.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.95/5.48  
% 11.95/5.48  Inference rules
% 11.95/5.48  ----------------------
% 11.95/5.48  #Ref     : 0
% 11.95/5.48  #Sup     : 9974
% 11.95/5.48  #Fact    : 0
% 11.95/5.48  #Define  : 0
% 11.95/5.48  #Split   : 5
% 11.95/5.48  #Chain   : 0
% 11.95/5.48  #Close   : 0
% 11.95/5.48  
% 11.95/5.48  Ordering : KBO
% 11.95/5.48  
% 11.95/5.48  Simplification rules
% 11.95/5.48  ----------------------
% 11.95/5.48  #Subsume      : 345
% 11.95/5.48  #Demod        : 9848
% 11.95/5.48  #Tautology    : 7148
% 11.95/5.48  #SimpNegUnit  : 7
% 11.95/5.48  #BackRed      : 6
% 11.95/5.48  
% 11.95/5.48  #Partial instantiations: 0
% 11.95/5.48  #Strategies tried      : 1
% 11.95/5.48  
% 11.95/5.48  Timing (in seconds)
% 11.95/5.48  ----------------------
% 11.95/5.48  Preprocessing        : 0.36
% 11.95/5.48  Parsing              : 0.19
% 11.95/5.48  CNF conversion       : 0.02
% 11.95/5.48  Main loop            : 4.36
% 11.95/5.48  Inferencing          : 0.78
% 11.95/5.48  Reduction            : 2.43
% 11.95/5.48  Demodulation         : 2.10
% 11.95/5.48  BG Simplification    : 0.10
% 11.95/5.48  Subsumption          : 0.84
% 11.95/5.48  Abstraction          : 0.13
% 11.95/5.48  MUC search           : 0.00
% 11.95/5.48  Cooper               : 0.00
% 11.95/5.48  Total                : 4.75
% 11.95/5.48  Index Insertion      : 0.00
% 11.95/5.48  Index Deletion       : 0.00
% 11.95/5.48  Index Matching       : 0.00
% 11.95/5.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
