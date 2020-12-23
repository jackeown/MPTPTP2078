%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:23 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 314 expanded)
%              Number of leaves         :   27 ( 121 expanded)
%              Depth                    :    8
%              Number of atoms          :  314 (1319 expanded)
%              Number of equality atoms :   49 (  74 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v4_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v5_tops_1(D,B) )
                      & ( v5_tops_1(C,A)
                       => ( v4_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_52,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(c_44,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1804,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1871,plain,(
    ! [B_237,A_238] :
      ( v4_pre_topc(B_237,A_238)
      | k2_pre_topc(A_238,B_237) != B_237
      | ~ v2_pre_topc(A_238)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ l1_pre_topc(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1877,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1871])).

tff(c_1884,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_1877])).

tff(c_1885,plain,(
    k2_pre_topc('#skF_1','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1804,c_1884])).

tff(c_46,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_53,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_64,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_152,plain,(
    ! [B_52,A_53] :
      ( v4_pre_topc(B_52,A_53)
      | k2_pre_topc(A_53,B_52) != B_52
      | ~ v2_pre_topc(A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != '#skF_3'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_152])).

tff(c_165,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | k2_pre_topc('#skF_1','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_158])).

tff(c_166,plain,(
    k2_pre_topc('#skF_1','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_165])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_128,plain,(
    ! [A_48,B_49] :
      ( k2_pre_topc(A_48,k1_tops_1(A_48,B_49)) = B_49
      | ~ v5_tops_1(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_132,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_138,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_132])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tops_1(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( k2_pre_topc(A_46,k2_pre_topc(A_46,B_47)) = k2_pre_topc(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_205,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,k2_pre_topc(A_60,k1_tops_1(A_60,B_61))) = k2_pre_topc(A_60,k1_tops_1(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_209,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_205])).

tff(c_215,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_138,c_138,c_209])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_215])).

tff(c_218,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_220,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_225,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tops_1(A_62,B_63),B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_227,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_225])).

tff(c_232,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_227])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_308,plain,(
    ! [A_74,B_75] :
      ( k2_pre_topc(A_74,k1_tops_1(A_74,B_75)) = B_75
      | ~ v5_tops_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_312,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_308])).

tff(c_318,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_312])).

tff(c_219,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_244,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,B_65) = B_65
      | ~ v4_pre_topc(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_247,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_244])).

tff(c_253,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_219,c_247])).

tff(c_450,plain,(
    ! [B_95,A_96] :
      ( v4_tops_1(B_95,A_96)
      | ~ r1_tarski(B_95,k2_pre_topc(A_96,k1_tops_1(A_96,B_95)))
      | ~ r1_tarski(k1_tops_1(A_96,k2_pre_topc(A_96,B_95)),B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_465,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_450])).

tff(c_474,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_232,c_6,c_318,c_465])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_474])).

tff(c_477,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_478,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_482,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_478,c_42])).

tff(c_483,plain,(
    ! [A_97,B_98] :
      ( r1_tarski(k1_tops_1(A_97,B_98),B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_487,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_483])).

tff(c_493,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_487])).

tff(c_618,plain,(
    ! [A_117,C_118,B_119] :
      ( r1_tarski(k2_pre_topc(A_117,C_118),B_119)
      | ~ r1_tarski(C_118,B_119)
      | ~ v4_pre_topc(B_119,A_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1274,plain,(
    ! [A_163,B_164,B_165] :
      ( r1_tarski(k2_pre_topc(A_163,k1_tops_1(A_163,B_164)),B_165)
      | ~ r1_tarski(k1_tops_1(A_163,B_164),B_165)
      | ~ v4_pre_topc(B_165,A_163)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_24,c_618])).

tff(c_577,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,k2_pre_topc(A_112,k1_tops_1(A_112,B_111)))
      | ~ v4_tops_1(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_580,plain,(
    ! [A_112,B_111] :
      ( k2_pre_topc(A_112,k1_tops_1(A_112,B_111)) = B_111
      | ~ r1_tarski(k2_pre_topc(A_112,k1_tops_1(A_112,B_111)),B_111)
      | ~ v4_tops_1(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_577,c_2])).

tff(c_1341,plain,(
    ! [A_171,B_172] :
      ( k2_pre_topc(A_171,k1_tops_1(A_171,B_172)) = B_172
      | ~ v4_tops_1(B_172,A_171)
      | ~ r1_tarski(k1_tops_1(A_171,B_172),B_172)
      | ~ v4_pre_topc(B_172,A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_1274,c_580])).

tff(c_1349,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_493,c_1341])).

tff(c_1361,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_477,c_482,c_1349])).

tff(c_20,plain,(
    ! [B_13,A_11] :
      ( v5_tops_1(B_13,A_11)
      | k2_pre_topc(A_11,k1_tops_1(A_11,B_13)) != B_13
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1401,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_20])).

tff(c_1418,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1401])).

tff(c_1420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1418])).

tff(c_1421,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1422,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1423,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1422,c_48])).

tff(c_1433,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(k1_tops_1(A_177,B_178),B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1437,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1433])).

tff(c_1443,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1437])).

tff(c_1551,plain,(
    ! [A_197,C_198,B_199] :
      ( r1_tarski(k2_pre_topc(A_197,C_198),B_199)
      | ~ r1_tarski(C_198,B_199)
      | ~ v4_pre_topc(B_199,A_197)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1723,plain,(
    ! [A_220,B_221,B_222] :
      ( r1_tarski(k2_pre_topc(A_220,k1_tops_1(A_220,B_221)),B_222)
      | ~ r1_tarski(k1_tops_1(A_220,B_221),B_222)
      | ~ v4_pre_topc(B_222,A_220)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(resolution,[status(thm)],[c_24,c_1551])).

tff(c_1533,plain,(
    ! [B_193,A_194] :
      ( r1_tarski(B_193,k2_pre_topc(A_194,k1_tops_1(A_194,B_193)))
      | ~ v4_tops_1(B_193,A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1536,plain,(
    ! [A_194,B_193] :
      ( k2_pre_topc(A_194,k1_tops_1(A_194,B_193)) = B_193
      | ~ r1_tarski(k2_pre_topc(A_194,k1_tops_1(A_194,B_193)),B_193)
      | ~ v4_tops_1(B_193,A_194)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(resolution,[status(thm)],[c_1533,c_2])).

tff(c_1737,plain,(
    ! [A_223,B_224] :
      ( k2_pre_topc(A_223,k1_tops_1(A_223,B_224)) = B_224
      | ~ v4_tops_1(B_224,A_223)
      | ~ r1_tarski(k1_tops_1(A_223,B_224),B_224)
      | ~ v4_pre_topc(B_224,A_223)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(resolution,[status(thm)],[c_1723,c_1536])).

tff(c_1743,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1443,c_1737])).

tff(c_1750,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1421,c_1423,c_1743])).

tff(c_1773,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1750,c_20])).

tff(c_1790,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1773])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1790])).

tff(c_1793,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1891,plain,(
    ! [A_239,B_240] :
      ( k2_pre_topc(A_239,k1_tops_1(A_239,B_240)) = B_240
      | ~ v5_tops_1(B_240,A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1895,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1891])).

tff(c_1901,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1793,c_1895])).

tff(c_1848,plain,(
    ! [A_233,B_234] :
      ( k2_pre_topc(A_233,k2_pre_topc(A_233,B_234)) = k2_pre_topc(A_233,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1965,plain,(
    ! [A_247,B_248] :
      ( k2_pre_topc(A_247,k2_pre_topc(A_247,k1_tops_1(A_247,B_248))) = k2_pre_topc(A_247,k1_tops_1(A_247,B_248))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(resolution,[status(thm)],[c_24,c_1848])).

tff(c_1969,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1965])).

tff(c_1975,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1901,c_1901,c_1969])).

tff(c_1977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1885,c_1975])).

tff(c_1979,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1978,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1986,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1978])).

tff(c_1989,plain,(
    ! [A_249,B_250] :
      ( r1_tarski(k1_tops_1(A_249,B_250),B_250)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1991,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1989])).

tff(c_1996,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1991])).

tff(c_2052,plain,(
    ! [A_257,B_258] :
      ( k2_pre_topc(A_257,k1_tops_1(A_257,B_258)) = B_258
      | ~ v5_tops_1(B_258,A_257)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2056,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2052])).

tff(c_2062,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1793,c_2056])).

tff(c_2008,plain,(
    ! [A_251,B_252] :
      ( k2_pre_topc(A_251,B_252) = B_252
      | ~ v4_pre_topc(B_252,A_251)
      | ~ m1_subset_1(B_252,k1_zfmisc_1(u1_struct_0(A_251)))
      | ~ l1_pre_topc(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2011,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2008])).

tff(c_2017,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1979,c_2011])).

tff(c_2218,plain,(
    ! [B_280,A_281] :
      ( v4_tops_1(B_280,A_281)
      | ~ r1_tarski(B_280,k2_pre_topc(A_281,k1_tops_1(A_281,B_280)))
      | ~ r1_tarski(k1_tops_1(A_281,k2_pre_topc(A_281,B_280)),B_280)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2233,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_2218])).

tff(c_2242,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1996,c_6,c_2062,c_2233])).

tff(c_2244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1986,c_2242])).

tff(c_2246,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1978])).

tff(c_1794,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1979,c_2246,c_1794,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.84  
% 4.47/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.84  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.47/1.84  
% 4.47/1.84  %Foreground sorts:
% 4.47/1.84  
% 4.47/1.84  
% 4.47/1.84  %Background operators:
% 4.47/1.84  
% 4.47/1.84  
% 4.47/1.84  %Foreground operators:
% 4.47/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.47/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.84  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 4.47/1.84  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.47/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.84  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.47/1.84  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 4.47/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.47/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.47/1.84  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.47/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.84  
% 4.65/1.87  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tops_1)).
% 4.65/1.87  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.65/1.87  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 4.65/1.87  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.65/1.87  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 4.65/1.87  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.65/1.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.65/1.87  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 4.65/1.87  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 4.65/1.87  tff(c_44, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_1804, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_1871, plain, (![B_237, A_238]: (v4_pre_topc(B_237, A_238) | k2_pre_topc(A_238, B_237)!=B_237 | ~v2_pre_topc(A_238) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_238))) | ~l1_pre_topc(A_238))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_1877, plain, (v4_pre_topc('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1871])).
% 4.65/1.87  tff(c_1884, plain, (v4_pre_topc('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_1877])).
% 4.65/1.87  tff(c_1885, plain, (k2_pre_topc('#skF_1', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1804, c_1884])).
% 4.65/1.87  tff(c_46, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_53, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.65/1.87  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_64, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_152, plain, (![B_52, A_53]: (v4_pre_topc(B_52, A_53) | k2_pre_topc(A_53, B_52)!=B_52 | ~v2_pre_topc(A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_158, plain, (v4_pre_topc('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!='#skF_3' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_152])).
% 4.65/1.87  tff(c_165, plain, (v4_pre_topc('#skF_3', '#skF_1') | k2_pre_topc('#skF_1', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_158])).
% 4.65/1.87  tff(c_166, plain, (k2_pre_topc('#skF_1', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_64, c_165])).
% 4.65/1.87  tff(c_50, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_54, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 4.65/1.87  tff(c_128, plain, (![A_48, B_49]: (k2_pre_topc(A_48, k1_tops_1(A_48, B_49))=B_49 | ~v5_tops_1(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.87  tff(c_132, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_128])).
% 4.65/1.87  tff(c_138, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_132])).
% 4.65/1.87  tff(c_24, plain, (![A_14, B_15]: (m1_subset_1(k1_tops_1(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.65/1.87  tff(c_106, plain, (![A_46, B_47]: (k2_pre_topc(A_46, k2_pre_topc(A_46, B_47))=k2_pre_topc(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.87  tff(c_205, plain, (![A_60, B_61]: (k2_pre_topc(A_60, k2_pre_topc(A_60, k1_tops_1(A_60, B_61)))=k2_pre_topc(A_60, k1_tops_1(A_60, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_24, c_106])).
% 4.65/1.87  tff(c_209, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_205])).
% 4.65/1.87  tff(c_215, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_138, c_138, c_209])).
% 4.65/1.87  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_215])).
% 4.65/1.87  tff(c_218, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_220, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_218])).
% 4.65/1.87  tff(c_225, plain, (![A_62, B_63]: (r1_tarski(k1_tops_1(A_62, B_63), B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.65/1.87  tff(c_227, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_225])).
% 4.65/1.87  tff(c_232, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_227])).
% 4.65/1.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.87  tff(c_308, plain, (![A_74, B_75]: (k2_pre_topc(A_74, k1_tops_1(A_74, B_75))=B_75 | ~v5_tops_1(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.87  tff(c_312, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_308])).
% 4.65/1.87  tff(c_318, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54, c_312])).
% 4.65/1.87  tff(c_219, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_244, plain, (![A_64, B_65]: (k2_pre_topc(A_64, B_65)=B_65 | ~v4_pre_topc(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_247, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_244])).
% 4.65/1.87  tff(c_253, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_219, c_247])).
% 4.65/1.87  tff(c_450, plain, (![B_95, A_96]: (v4_tops_1(B_95, A_96) | ~r1_tarski(B_95, k2_pre_topc(A_96, k1_tops_1(A_96, B_95))) | ~r1_tarski(k1_tops_1(A_96, k2_pre_topc(A_96, B_95)), B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.87  tff(c_465, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_253, c_450])).
% 4.65/1.87  tff(c_474, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_232, c_6, c_318, c_465])).
% 4.65/1.87  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_474])).
% 4.65/1.87  tff(c_477, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_218])).
% 4.65/1.87  tff(c_478, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_218])).
% 4.65/1.87  tff(c_42, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_482, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_478, c_42])).
% 4.65/1.87  tff(c_483, plain, (![A_97, B_98]: (r1_tarski(k1_tops_1(A_97, B_98), B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.65/1.87  tff(c_487, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_483])).
% 4.65/1.87  tff(c_493, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_487])).
% 4.65/1.87  tff(c_618, plain, (![A_117, C_118, B_119]: (r1_tarski(k2_pre_topc(A_117, C_118), B_119) | ~r1_tarski(C_118, B_119) | ~v4_pre_topc(B_119, A_117) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.65/1.87  tff(c_1274, plain, (![A_163, B_164, B_165]: (r1_tarski(k2_pre_topc(A_163, k1_tops_1(A_163, B_164)), B_165) | ~r1_tarski(k1_tops_1(A_163, B_164), B_165) | ~v4_pre_topc(B_165, A_163) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_163))) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_24, c_618])).
% 4.65/1.87  tff(c_577, plain, (![B_111, A_112]: (r1_tarski(B_111, k2_pre_topc(A_112, k1_tops_1(A_112, B_111))) | ~v4_tops_1(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.87  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.87  tff(c_580, plain, (![A_112, B_111]: (k2_pre_topc(A_112, k1_tops_1(A_112, B_111))=B_111 | ~r1_tarski(k2_pre_topc(A_112, k1_tops_1(A_112, B_111)), B_111) | ~v4_tops_1(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(resolution, [status(thm)], [c_577, c_2])).
% 4.65/1.87  tff(c_1341, plain, (![A_171, B_172]: (k2_pre_topc(A_171, k1_tops_1(A_171, B_172))=B_172 | ~v4_tops_1(B_172, A_171) | ~r1_tarski(k1_tops_1(A_171, B_172), B_172) | ~v4_pre_topc(B_172, A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_1274, c_580])).
% 4.65/1.87  tff(c_1349, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_493, c_1341])).
% 4.65/1.87  tff(c_1361, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_477, c_482, c_1349])).
% 4.65/1.87  tff(c_20, plain, (![B_13, A_11]: (v5_tops_1(B_13, A_11) | k2_pre_topc(A_11, k1_tops_1(A_11, B_13))!=B_13 | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.87  tff(c_1401, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1361, c_20])).
% 4.65/1.87  tff(c_1418, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1401])).
% 4.65/1.87  tff(c_1420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1418])).
% 4.65/1.87  tff(c_1421, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.65/1.87  tff(c_1422, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.65/1.87  tff(c_48, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_1423, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1422, c_48])).
% 4.65/1.87  tff(c_1433, plain, (![A_177, B_178]: (r1_tarski(k1_tops_1(A_177, B_178), B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.65/1.87  tff(c_1437, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1433])).
% 4.65/1.87  tff(c_1443, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1437])).
% 4.65/1.87  tff(c_1551, plain, (![A_197, C_198, B_199]: (r1_tarski(k2_pre_topc(A_197, C_198), B_199) | ~r1_tarski(C_198, B_199) | ~v4_pre_topc(B_199, A_197) | ~m1_subset_1(C_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.65/1.87  tff(c_1723, plain, (![A_220, B_221, B_222]: (r1_tarski(k2_pre_topc(A_220, k1_tops_1(A_220, B_221)), B_222) | ~r1_tarski(k1_tops_1(A_220, B_221), B_222) | ~v4_pre_topc(B_222, A_220) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_220))) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(resolution, [status(thm)], [c_24, c_1551])).
% 4.65/1.87  tff(c_1533, plain, (![B_193, A_194]: (r1_tarski(B_193, k2_pre_topc(A_194, k1_tops_1(A_194, B_193))) | ~v4_tops_1(B_193, A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.87  tff(c_1536, plain, (![A_194, B_193]: (k2_pre_topc(A_194, k1_tops_1(A_194, B_193))=B_193 | ~r1_tarski(k2_pre_topc(A_194, k1_tops_1(A_194, B_193)), B_193) | ~v4_tops_1(B_193, A_194) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(resolution, [status(thm)], [c_1533, c_2])).
% 4.65/1.87  tff(c_1737, plain, (![A_223, B_224]: (k2_pre_topc(A_223, k1_tops_1(A_223, B_224))=B_224 | ~v4_tops_1(B_224, A_223) | ~r1_tarski(k1_tops_1(A_223, B_224), B_224) | ~v4_pre_topc(B_224, A_223) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(resolution, [status(thm)], [c_1723, c_1536])).
% 4.65/1.87  tff(c_1743, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~v4_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1443, c_1737])).
% 4.65/1.87  tff(c_1750, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1421, c_1423, c_1743])).
% 4.65/1.87  tff(c_1773, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1750, c_20])).
% 4.65/1.87  tff(c_1790, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1773])).
% 4.65/1.87  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1790])).
% 4.65/1.87  tff(c_1793, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.65/1.87  tff(c_1891, plain, (![A_239, B_240]: (k2_pre_topc(A_239, k1_tops_1(A_239, B_240))=B_240 | ~v5_tops_1(B_240, A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.87  tff(c_1895, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1891])).
% 4.65/1.87  tff(c_1901, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1793, c_1895])).
% 4.65/1.87  tff(c_1848, plain, (![A_233, B_234]: (k2_pre_topc(A_233, k2_pre_topc(A_233, B_234))=k2_pre_topc(A_233, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.65/1.87  tff(c_1965, plain, (![A_247, B_248]: (k2_pre_topc(A_247, k2_pre_topc(A_247, k1_tops_1(A_247, B_248)))=k2_pre_topc(A_247, k1_tops_1(A_247, B_248)) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(resolution, [status(thm)], [c_24, c_1848])).
% 4.65/1.87  tff(c_1969, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1965])).
% 4.65/1.87  tff(c_1975, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1901, c_1901, c_1969])).
% 4.65/1.87  tff(c_1977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1885, c_1975])).
% 4.65/1.87  tff(c_1979, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_1978, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_1986, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1978])).
% 4.65/1.87  tff(c_1989, plain, (![A_249, B_250]: (r1_tarski(k1_tops_1(A_249, B_250), B_250) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.65/1.87  tff(c_1991, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1989])).
% 4.65/1.87  tff(c_1996, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1991])).
% 4.65/1.87  tff(c_2052, plain, (![A_257, B_258]: (k2_pre_topc(A_257, k1_tops_1(A_257, B_258))=B_258 | ~v5_tops_1(B_258, A_257) | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0(A_257))) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.65/1.87  tff(c_2056, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2052])).
% 4.65/1.87  tff(c_2062, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1793, c_2056])).
% 4.65/1.87  tff(c_2008, plain, (![A_251, B_252]: (k2_pre_topc(A_251, B_252)=B_252 | ~v4_pre_topc(B_252, A_251) | ~m1_subset_1(B_252, k1_zfmisc_1(u1_struct_0(A_251))) | ~l1_pre_topc(A_251))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_2011, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2008])).
% 4.65/1.87  tff(c_2017, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1979, c_2011])).
% 4.65/1.87  tff(c_2218, plain, (![B_280, A_281]: (v4_tops_1(B_280, A_281) | ~r1_tarski(B_280, k2_pre_topc(A_281, k1_tops_1(A_281, B_280))) | ~r1_tarski(k1_tops_1(A_281, k2_pre_topc(A_281, B_280)), B_280) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.87  tff(c_2233, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2017, c_2218])).
% 4.65/1.87  tff(c_2242, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1996, c_6, c_2062, c_2233])).
% 4.65/1.87  tff(c_2244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1986, c_2242])).
% 4.65/1.87  tff(c_2246, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1978])).
% 4.65/1.87  tff(c_1794, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 4.65/1.87  tff(c_40, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_2250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1979, c_2246, c_1794, c_40])).
% 4.65/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.87  
% 4.65/1.87  Inference rules
% 4.65/1.87  ----------------------
% 4.65/1.87  #Ref     : 0
% 4.65/1.87  #Sup     : 445
% 4.65/1.87  #Fact    : 0
% 4.65/1.87  #Define  : 0
% 4.65/1.87  #Split   : 65
% 4.65/1.87  #Chain   : 0
% 4.65/1.87  #Close   : 0
% 4.65/1.87  
% 4.65/1.87  Ordering : KBO
% 4.65/1.87  
% 4.65/1.87  Simplification rules
% 4.65/1.87  ----------------------
% 4.65/1.87  #Subsume      : 65
% 4.65/1.87  #Demod        : 614
% 4.65/1.87  #Tautology    : 167
% 4.65/1.87  #SimpNegUnit  : 24
% 4.65/1.87  #BackRed      : 18
% 4.65/1.87  
% 4.65/1.87  #Partial instantiations: 0
% 4.65/1.87  #Strategies tried      : 1
% 4.65/1.87  
% 4.65/1.87  Timing (in seconds)
% 4.65/1.87  ----------------------
% 4.65/1.87  Preprocessing        : 0.31
% 4.65/1.87  Parsing              : 0.16
% 4.65/1.87  CNF conversion       : 0.02
% 4.65/1.87  Main loop            : 0.72
% 4.65/1.87  Inferencing          : 0.24
% 4.65/1.87  Reduction            : 0.24
% 4.65/1.87  Demodulation         : 0.17
% 4.65/1.87  BG Simplification    : 0.03
% 4.65/1.87  Subsumption          : 0.15
% 4.65/1.87  Abstraction          : 0.04
% 4.65/1.87  MUC search           : 0.00
% 4.65/1.87  Cooper               : 0.00
% 4.65/1.87  Total                : 1.09
% 4.65/1.87  Index Insertion      : 0.00
% 4.65/1.87  Index Deletion       : 0.00
% 4.65/1.87  Index Matching       : 0.00
% 4.65/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
