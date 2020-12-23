%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:53 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 178 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 593 expanded)
%              Number of equality atoms :   31 (  93 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_65,plain,(
    ! [B_51,A_52] :
      ( v2_tops_1(B_51,A_52)
      | k1_tops_1(A_52,B_51) != k1_xboole_0
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_71,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_79,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_71])).

tff(c_80,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_79])).

tff(c_50,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tops_1(A_46,B_47),B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_50])).

tff(c_58,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_98,plain,(
    ! [A_55,B_56] :
      ( v3_pre_topc(k1_tops_1(A_55,B_56),A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_98])).

tff(c_109,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_102])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tops_1(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [C_43] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_43
      | ~ v3_pre_topc(C_43,'#skF_2')
      | ~ r1_tarski(C_43,'#skF_3')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_122,plain,(
    ! [C_60] :
      ( k1_xboole_0 = C_60
      | ~ v3_pre_topc(C_60,'#skF_2')
      | ~ r1_tarski(C_60,'#skF_3')
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46])).

tff(c_126,plain,(
    ! [B_5] :
      ( k1_tops_1('#skF_2',B_5) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_5),'#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_5),'#skF_3')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_159,plain,(
    ! [B_72] :
      ( k1_tops_1('#skF_2',B_72) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_72),'#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_72),'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126])).

tff(c_166,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_159])).

tff(c_176,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_109,c_166])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_176])).

tff(c_179,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_180,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_185,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_30])).

tff(c_34,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_187,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_34])).

tff(c_277,plain,(
    ! [B_84,A_85] :
      ( v2_tops_1(B_84,A_85)
      | k1_tops_1(A_85,B_84) != k1_xboole_0
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_286,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | k1_tops_1('#skF_2','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_187,c_277])).

tff(c_300,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | k1_tops_1('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_286])).

tff(c_327,plain,(
    k1_tops_1('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_32,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_183,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_32])).

tff(c_228,plain,(
    ! [A_82,B_83] :
      ( k1_tops_1(A_82,B_83) = k1_xboole_0
      | ~ v2_tops_1(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_237,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_248,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_180,c_237])).

tff(c_397,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski(k1_tops_1(A_94,B_95),k1_tops_1(A_94,C_96))
      | ~ r1_tarski(B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_409,plain,(
    ! [B_95] :
      ( r1_tarski(k1_tops_1('#skF_2',B_95),k1_xboole_0)
      | ~ r1_tarski(B_95,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_397])).

tff(c_446,plain,(
    ! [B_98] :
      ( r1_tarski(k1_tops_1('#skF_2',B_98),k1_xboole_0)
      | ~ r1_tarski(B_98,'#skF_3')
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_409])).

tff(c_456,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_446])).

tff(c_472,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_456])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_478,plain,(
    k1_tops_1('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_472,c_2])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_478])).

tff(c_484,plain,(
    k1_tops_1('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_255,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_6])).

tff(c_259,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_255])).

tff(c_16,plain,(
    ! [B_26,D_32,C_30,A_18] :
      ( k1_tops_1(B_26,D_32) = D_32
      | ~ v3_pre_topc(D_32,B_26)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_973,plain,(
    ! [C_127,A_128] :
      ( ~ m1_subset_1(C_127,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_976,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_259,c_973])).

tff(c_992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_976])).

tff(c_994,plain,(
    ! [B_129,D_130] :
      ( k1_tops_1(B_129,D_130) = D_130
      | ~ v3_pre_topc(D_130,B_129)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(u1_struct_0(B_129)))
      | ~ l1_pre_topc(B_129) ) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1003,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_187,c_994])).

tff(c_1017,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_185,c_484,c_1003])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_1017])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.51  
% 2.99/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.51  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.99/1.51  
% 2.99/1.51  %Foreground sorts:
% 2.99/1.51  
% 2.99/1.51  
% 2.99/1.51  %Background operators:
% 2.99/1.51  
% 2.99/1.51  
% 2.99/1.51  %Foreground operators:
% 2.99/1.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.99/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.99/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.51  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.99/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.99/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.99/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.99/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.99/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.51  
% 2.99/1.53  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 2.99/1.53  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 2.99/1.53  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.99/1.53  tff(f_46, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.99/1.53  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.99/1.53  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 2.99/1.53  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.99/1.53  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 2.99/1.53  tff(c_28, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_48, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 2.99/1.53  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_65, plain, (![B_51, A_52]: (v2_tops_1(B_51, A_52) | k1_tops_1(A_52, B_51)!=k1_xboole_0 | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.53  tff(c_71, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_65])).
% 2.99/1.53  tff(c_79, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_71])).
% 2.99/1.53  tff(c_80, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_79])).
% 2.99/1.53  tff(c_50, plain, (![A_46, B_47]: (r1_tarski(k1_tops_1(A_46, B_47), B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.99/1.53  tff(c_52, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_50])).
% 2.99/1.53  tff(c_58, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52])).
% 2.99/1.53  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_98, plain, (![A_55, B_56]: (v3_pre_topc(k1_tops_1(A_55, B_56), A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.99/1.53  tff(c_102, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_98])).
% 2.99/1.53  tff(c_109, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_102])).
% 2.99/1.53  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(k1_tops_1(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.53  tff(c_46, plain, (![C_43]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_43 | ~v3_pre_topc(C_43, '#skF_2') | ~r1_tarski(C_43, '#skF_3') | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_122, plain, (![C_60]: (k1_xboole_0=C_60 | ~v3_pre_topc(C_60, '#skF_2') | ~r1_tarski(C_60, '#skF_3') | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_46])).
% 2.99/1.53  tff(c_126, plain, (![B_5]: (k1_tops_1('#skF_2', B_5)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_2', B_5), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', B_5), '#skF_3') | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.99/1.53  tff(c_159, plain, (![B_72]: (k1_tops_1('#skF_2', B_72)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_2', B_72), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', B_72), '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_126])).
% 2.99/1.53  tff(c_166, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_22, c_159])).
% 2.99/1.53  tff(c_176, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_109, c_166])).
% 2.99/1.53  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_176])).
% 2.99/1.53  tff(c_179, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_28])).
% 2.99/1.53  tff(c_180, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.99/1.53  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_185, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_30])).
% 2.99/1.53  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_187, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_34])).
% 2.99/1.53  tff(c_277, plain, (![B_84, A_85]: (v2_tops_1(B_84, A_85) | k1_tops_1(A_85, B_84)!=k1_xboole_0 | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.53  tff(c_286, plain, (v2_tops_1('#skF_4', '#skF_2') | k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_187, c_277])).
% 2.99/1.53  tff(c_300, plain, (v2_tops_1('#skF_4', '#skF_2') | k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_286])).
% 2.99/1.53  tff(c_327, plain, (k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_300])).
% 2.99/1.53  tff(c_32, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.99/1.53  tff(c_183, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_32])).
% 2.99/1.53  tff(c_228, plain, (![A_82, B_83]: (k1_tops_1(A_82, B_83)=k1_xboole_0 | ~v2_tops_1(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.53  tff(c_237, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_228])).
% 2.99/1.53  tff(c_248, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_180, c_237])).
% 2.99/1.53  tff(c_397, plain, (![A_94, B_95, C_96]: (r1_tarski(k1_tops_1(A_94, B_95), k1_tops_1(A_94, C_96)) | ~r1_tarski(B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.53  tff(c_409, plain, (![B_95]: (r1_tarski(k1_tops_1('#skF_2', B_95), k1_xboole_0) | ~r1_tarski(B_95, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_248, c_397])).
% 2.99/1.53  tff(c_446, plain, (![B_98]: (r1_tarski(k1_tops_1('#skF_2', B_98), k1_xboole_0) | ~r1_tarski(B_98, '#skF_3') | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_409])).
% 2.99/1.53  tff(c_456, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_187, c_446])).
% 2.99/1.53  tff(c_472, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_456])).
% 2.99/1.53  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.53  tff(c_478, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_472, c_2])).
% 2.99/1.53  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_478])).
% 2.99/1.53  tff(c_484, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_300])).
% 2.99/1.53  tff(c_255, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_248, c_6])).
% 2.99/1.53  tff(c_259, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_255])).
% 2.99/1.53  tff(c_16, plain, (![B_26, D_32, C_30, A_18]: (k1_tops_1(B_26, D_32)=D_32 | ~v3_pre_topc(D_32, B_26) | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0(B_26))) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.99/1.53  tff(c_973, plain, (![C_127, A_128]: (~m1_subset_1(C_127, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(splitLeft, [status(thm)], [c_16])).
% 2.99/1.53  tff(c_976, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_259, c_973])).
% 2.99/1.53  tff(c_992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_976])).
% 2.99/1.53  tff(c_994, plain, (![B_129, D_130]: (k1_tops_1(B_129, D_130)=D_130 | ~v3_pre_topc(D_130, B_129) | ~m1_subset_1(D_130, k1_zfmisc_1(u1_struct_0(B_129))) | ~l1_pre_topc(B_129))), inference(splitRight, [status(thm)], [c_16])).
% 2.99/1.53  tff(c_1003, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_187, c_994])).
% 2.99/1.53  tff(c_1017, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_185, c_484, c_1003])).
% 2.99/1.53  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_1017])).
% 2.99/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.53  
% 2.99/1.53  Inference rules
% 2.99/1.53  ----------------------
% 2.99/1.53  #Ref     : 0
% 2.99/1.53  #Sup     : 174
% 2.99/1.53  #Fact    : 0
% 2.99/1.53  #Define  : 0
% 2.99/1.53  #Split   : 19
% 2.99/1.53  #Chain   : 0
% 2.99/1.53  #Close   : 0
% 2.99/1.53  
% 2.99/1.53  Ordering : KBO
% 2.99/1.53  
% 2.99/1.53  Simplification rules
% 2.99/1.53  ----------------------
% 2.99/1.53  #Subsume      : 21
% 2.99/1.53  #Demod        : 346
% 2.99/1.53  #Tautology    : 87
% 2.99/1.53  #SimpNegUnit  : 6
% 2.99/1.53  #BackRed      : 6
% 2.99/1.53  
% 2.99/1.53  #Partial instantiations: 0
% 2.99/1.53  #Strategies tried      : 1
% 2.99/1.53  
% 2.99/1.53  Timing (in seconds)
% 2.99/1.53  ----------------------
% 3.23/1.53  Preprocessing        : 0.32
% 3.23/1.53  Parsing              : 0.17
% 3.23/1.53  CNF conversion       : 0.02
% 3.23/1.53  Main loop            : 0.41
% 3.23/1.53  Inferencing          : 0.15
% 3.23/1.53  Reduction            : 0.14
% 3.23/1.53  Demodulation         : 0.10
% 3.23/1.53  BG Simplification    : 0.02
% 3.23/1.53  Subsumption          : 0.08
% 3.23/1.53  Abstraction          : 0.02
% 3.23/1.53  MUC search           : 0.00
% 3.23/1.53  Cooper               : 0.00
% 3.23/1.53  Total                : 0.77
% 3.23/1.53  Index Insertion      : 0.00
% 3.23/1.53  Index Deletion       : 0.00
% 3.23/1.53  Index Matching       : 0.00
% 3.23/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
