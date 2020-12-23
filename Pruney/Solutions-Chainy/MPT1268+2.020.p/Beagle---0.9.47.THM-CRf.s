%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 193 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  182 ( 644 expanded)
%              Number of equality atoms :   34 ( 102 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_54,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_113,plain,(
    ! [B_57,A_58] :
      ( v2_tops_1(B_57,A_58)
      | k1_tops_1(A_58,B_57) != k1_xboole_0
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_119,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_113])).

tff(c_123,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_119])).

tff(c_124,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_123])).

tff(c_78,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tops_1(A_49,B_50),B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_83,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_80])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_88,plain,(
    ! [A_51,B_52] :
      ( v3_pre_topc(k1_tops_1(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_93,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_90])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k1_tops_1(A_4,B_5),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [C_43] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_43
      | ~ v3_pre_topc(C_43,'#skF_1')
      | ~ r1_tarski(C_43,'#skF_2')
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_132,plain,(
    ! [C_59] :
      ( k1_xboole_0 = C_59
      | ~ v3_pre_topc(C_59,'#skF_1')
      | ~ r1_tarski(C_59,'#skF_2')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50])).

tff(c_136,plain,(
    ! [B_5] :
      ( k1_tops_1('#skF_1',B_5) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_5),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_5),'#skF_2')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_162,plain,(
    ! [B_66] :
      ( k1_tops_1('#skF_1',B_66) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_66),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_66),'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_136])).

tff(c_169,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_162])).

tff(c_175,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_93,c_169])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_175])).

tff(c_178,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_179,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_181,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_34])).

tff(c_38,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_212,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_38])).

tff(c_250,plain,(
    ! [A_76,B_77] :
      ( k1_tops_1(A_76,B_77) = k1_xboole_0
      | ~ v2_tops_1(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_256,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_212,c_250])).

tff(c_263,plain,
    ( k1_tops_1('#skF_1','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_256])).

tff(c_343,plain,(
    ~ v2_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_280,plain,(
    ! [B_78,A_79] :
      ( v2_tops_1(B_78,A_79)
      | k1_tops_1(A_79,B_78) != k1_xboole_0
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_286,plain,
    ( v2_tops_1('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_212,c_280])).

tff(c_293,plain,
    ( v2_tops_1('#skF_3','#skF_1')
    | k1_tops_1('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_286])).

tff(c_345,plain,(
    k1_tops_1('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_293])).

tff(c_36,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_183,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_36])).

tff(c_259,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_250])).

tff(c_266,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_179,c_259])).

tff(c_414,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(k1_tops_1(A_88,B_89),k1_tops_1(A_88,C_90))
      | ~ r1_tarski(B_89,C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_428,plain,(
    ! [B_89] :
      ( r1_tarski(k1_tops_1('#skF_1',B_89),k1_xboole_0)
      | ~ r1_tarski(B_89,'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_414])).

tff(c_439,plain,(
    ! [B_91] :
      ( r1_tarski(k1_tops_1('#skF_1',B_91),k1_xboole_0)
      | ~ r1_tarski(B_91,'#skF_2')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_428])).

tff(c_449,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_439])).

tff(c_461,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_449])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_184,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_196,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_184])).

tff(c_467,plain,(
    k1_tops_1('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_461,c_196])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_467])).

tff(c_474,plain,(
    k1_tops_1('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_274,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_10])).

tff(c_278,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_274])).

tff(c_20,plain,(
    ! [B_26,D_32,C_30,A_18] :
      ( k1_tops_1(B_26,D_32) = D_32
      | ~ v3_pre_topc(D_32,B_26)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0(B_26)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(B_26)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_781,plain,(
    ! [C_112,A_113] :
      ( ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_784,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_278,c_781])).

tff(c_797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_784])).

tff(c_799,plain,(
    ! [B_114,D_115] :
      ( k1_tops_1(B_114,D_115) = D_115
      | ~ v3_pre_topc(D_115,B_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(B_114)))
      | ~ l1_pre_topc(B_114) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_808,plain,
    ( k1_tops_1('#skF_1','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_212,c_799])).

tff(c_818,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_181,c_474,c_808])).

tff(c_820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:38:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.56  
% 2.97/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.57  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.57  
% 2.97/1.57  %Foreground sorts:
% 2.97/1.57  
% 2.97/1.57  
% 2.97/1.57  %Background operators:
% 2.97/1.57  
% 2.97/1.57  
% 2.97/1.57  %Foreground operators:
% 2.97/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.97/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.57  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.97/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.97/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.57  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.97/1.57  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.57  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.57  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.97/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.57  
% 2.97/1.58  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 2.97/1.58  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.97/1.58  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.97/1.58  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.97/1.58  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.97/1.58  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 2.97/1.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.97/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.97/1.58  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 2.97/1.58  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_54, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.97/1.58  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_113, plain, (![B_57, A_58]: (v2_tops_1(B_57, A_58) | k1_tops_1(A_58, B_57)!=k1_xboole_0 | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.97/1.58  tff(c_119, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_113])).
% 2.97/1.58  tff(c_123, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_119])).
% 2.97/1.58  tff(c_124, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_123])).
% 2.97/1.58  tff(c_78, plain, (![A_49, B_50]: (r1_tarski(k1_tops_1(A_49, B_50), B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.97/1.58  tff(c_80, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_78])).
% 2.97/1.58  tff(c_83, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_80])).
% 2.97/1.58  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_88, plain, (![A_51, B_52]: (v3_pre_topc(k1_tops_1(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.58  tff(c_90, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_88])).
% 2.97/1.58  tff(c_93, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_90])).
% 2.97/1.58  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(k1_tops_1(A_4, B_5), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.58  tff(c_50, plain, (![C_43]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_43 | ~v3_pre_topc(C_43, '#skF_1') | ~r1_tarski(C_43, '#skF_2') | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_132, plain, (![C_59]: (k1_xboole_0=C_59 | ~v3_pre_topc(C_59, '#skF_1') | ~r1_tarski(C_59, '#skF_2') | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_50])).
% 2.97/1.58  tff(c_136, plain, (![B_5]: (k1_tops_1('#skF_1', B_5)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_5), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_5), '#skF_2') | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_132])).
% 2.97/1.58  tff(c_162, plain, (![B_66]: (k1_tops_1('#skF_1', B_66)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_66), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_66), '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_136])).
% 2.97/1.58  tff(c_169, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_26, c_162])).
% 2.97/1.58  tff(c_175, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_83, c_93, c_169])).
% 2.97/1.58  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_175])).
% 2.97/1.58  tff(c_178, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.97/1.58  tff(c_179, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.97/1.58  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_181, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_34])).
% 2.97/1.58  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.58  tff(c_212, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_38])).
% 2.97/1.58  tff(c_250, plain, (![A_76, B_77]: (k1_tops_1(A_76, B_77)=k1_xboole_0 | ~v2_tops_1(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.97/1.58  tff(c_256, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_212, c_250])).
% 2.97/1.58  tff(c_263, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_256])).
% 2.97/1.58  tff(c_343, plain, (~v2_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_263])).
% 2.97/1.58  tff(c_280, plain, (![B_78, A_79]: (v2_tops_1(B_78, A_79) | k1_tops_1(A_79, B_78)!=k1_xboole_0 | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.97/1.58  tff(c_286, plain, (v2_tops_1('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_212, c_280])).
% 2.97/1.58  tff(c_293, plain, (v2_tops_1('#skF_3', '#skF_1') | k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_286])).
% 2.97/1.59  tff(c_345, plain, (k1_tops_1('#skF_1', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_343, c_293])).
% 2.97/1.59  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.97/1.59  tff(c_183, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_36])).
% 2.97/1.59  tff(c_259, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_250])).
% 2.97/1.59  tff(c_266, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_179, c_259])).
% 2.97/1.59  tff(c_414, plain, (![A_88, B_89, C_90]: (r1_tarski(k1_tops_1(A_88, B_89), k1_tops_1(A_88, C_90)) | ~r1_tarski(B_89, C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.97/1.59  tff(c_428, plain, (![B_89]: (r1_tarski(k1_tops_1('#skF_1', B_89), k1_xboole_0) | ~r1_tarski(B_89, '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_414])).
% 2.97/1.59  tff(c_439, plain, (![B_91]: (r1_tarski(k1_tops_1('#skF_1', B_91), k1_xboole_0) | ~r1_tarski(B_91, '#skF_2') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_428])).
% 2.97/1.59  tff(c_449, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_212, c_439])).
% 2.97/1.59  tff(c_461, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_183, c_449])).
% 2.97/1.59  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.59  tff(c_184, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.59  tff(c_196, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_184])).
% 2.97/1.59  tff(c_467, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_461, c_196])).
% 2.97/1.59  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_467])).
% 2.97/1.59  tff(c_474, plain, (k1_tops_1('#skF_1', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_263])).
% 2.97/1.59  tff(c_274, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_266, c_10])).
% 2.97/1.59  tff(c_278, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_274])).
% 2.97/1.59  tff(c_20, plain, (![B_26, D_32, C_30, A_18]: (k1_tops_1(B_26, D_32)=D_32 | ~v3_pre_topc(D_32, B_26) | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0(B_26))) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(B_26) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.97/1.59  tff(c_781, plain, (![C_112, A_113]: (~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(splitLeft, [status(thm)], [c_20])).
% 2.97/1.59  tff(c_784, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_278, c_781])).
% 2.97/1.59  tff(c_797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_784])).
% 2.97/1.59  tff(c_799, plain, (![B_114, D_115]: (k1_tops_1(B_114, D_115)=D_115 | ~v3_pre_topc(D_115, B_114) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(B_114))) | ~l1_pre_topc(B_114))), inference(splitRight, [status(thm)], [c_20])).
% 2.97/1.59  tff(c_808, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_212, c_799])).
% 2.97/1.59  tff(c_818, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_181, c_474, c_808])).
% 2.97/1.59  tff(c_820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_818])).
% 2.97/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.59  
% 2.97/1.59  Inference rules
% 2.97/1.59  ----------------------
% 2.97/1.59  #Ref     : 0
% 2.97/1.59  #Sup     : 139
% 2.97/1.59  #Fact    : 0
% 2.97/1.59  #Define  : 0
% 2.97/1.59  #Split   : 16
% 2.97/1.59  #Chain   : 0
% 2.97/1.59  #Close   : 0
% 2.97/1.59  
% 2.97/1.59  Ordering : KBO
% 2.97/1.59  
% 2.97/1.59  Simplification rules
% 2.97/1.59  ----------------------
% 2.97/1.59  #Subsume      : 25
% 2.97/1.59  #Demod        : 305
% 2.97/1.59  #Tautology    : 79
% 2.97/1.59  #SimpNegUnit  : 6
% 2.97/1.59  #BackRed      : 8
% 2.97/1.59  
% 2.97/1.59  #Partial instantiations: 0
% 2.97/1.59  #Strategies tried      : 1
% 2.97/1.59  
% 2.97/1.59  Timing (in seconds)
% 2.97/1.59  ----------------------
% 2.97/1.59  Preprocessing        : 0.39
% 2.97/1.59  Parsing              : 0.20
% 2.97/1.59  CNF conversion       : 0.03
% 2.97/1.59  Main loop            : 0.35
% 2.97/1.59  Inferencing          : 0.11
% 2.97/1.59  Reduction            : 0.12
% 2.97/1.59  Demodulation         : 0.09
% 2.97/1.59  BG Simplification    : 0.02
% 2.97/1.59  Subsumption          : 0.07
% 2.97/1.59  Abstraction          : 0.02
% 2.97/1.59  MUC search           : 0.00
% 2.97/1.59  Cooper               : 0.00
% 2.97/1.59  Total                : 0.78
% 2.97/1.59  Index Insertion      : 0.00
% 2.97/1.59  Index Deletion       : 0.00
% 2.97/1.59  Index Matching       : 0.00
% 2.97/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
