%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:48 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 786 expanded)
%              Number of leaves         :   29 ( 289 expanded)
%              Depth                    :   22
%              Number of atoms          :  321 (3154 expanded)
%              Number of equality atoms :   44 ( 348 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_100,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_152,plain,(
    ! [B_81,A_82] :
      ( v2_tops_1(B_81,A_82)
      | k1_tops_1(A_82,B_81) != k1_xboole_0
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_155,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_152])).

tff(c_158,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_155])).

tff(c_159,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_158])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_1,B_2,B_69] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_69)
      | ~ r1_tarski(A_1,B_69)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_191,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski('#skF_2'(A_94,B_95,C_96),C_96)
      | ~ r2_hidden(B_95,k1_tops_1(A_94,C_96))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_199,plain,(
    ! [A_94,C_96,B_2] :
      ( r1_tarski('#skF_2'(A_94,'#skF_1'(k1_tops_1(A_94,C_96),B_2),C_96),C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | r1_tarski(k1_tops_1(A_94,C_96),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_191])).

tff(c_184,plain,(
    ! [A_90,B_91,C_92] :
      ( v3_pre_topc('#skF_2'(A_90,B_91,C_92),A_90)
      | ~ r2_hidden(B_91,k1_tops_1(A_90,C_92))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_186,plain,(
    ! [B_91] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_91,'#skF_4'),'#skF_3')
      | ~ r2_hidden(B_91,k1_tops_1('#skF_3','#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_184])).

tff(c_189,plain,(
    ! [B_91] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_91,'#skF_4'),'#skF_3')
      | ~ r2_hidden(B_91,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_186])).

tff(c_216,plain,(
    ! [A_103,B_104,C_105] :
      ( m1_subset_1('#skF_2'(A_103,B_104,C_105),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ r2_hidden(B_104,k1_tops_1(A_103,C_105))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    ! [C_56] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_56
      | ~ v3_pre_topc(C_56,'#skF_3')
      | ~ r1_tarski(C_56,'#skF_4')
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_168,plain,(
    ! [C_56] :
      ( k1_xboole_0 = C_56
      | ~ v3_pre_topc(C_56,'#skF_3')
      | ~ r1_tarski(C_56,'#skF_4')
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_64])).

tff(c_222,plain,(
    ! [B_104,C_105] :
      ( '#skF_2'('#skF_3',B_104,C_105) = k1_xboole_0
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_104,C_105),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_3',B_104,C_105),'#skF_4')
      | ~ r2_hidden(B_104,k1_tops_1('#skF_3',C_105))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_216,c_168])).

tff(c_313,plain,(
    ! [B_125,C_126] :
      ( '#skF_2'('#skF_3',B_125,C_126) = k1_xboole_0
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_125,C_126),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_3',B_125,C_126),'#skF_4')
      | ~ r2_hidden(B_125,k1_tops_1('#skF_3',C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_222])).

tff(c_315,plain,(
    ! [B_91] :
      ( '#skF_2'('#skF_3',B_91,'#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_2'('#skF_3',B_91,'#skF_4'),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(B_91,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_189,c_313])).

tff(c_319,plain,(
    ! [B_127] :
      ( '#skF_2'('#skF_3',B_127,'#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_2'('#skF_3',B_127,'#skF_4'),'#skF_4')
      | ~ r2_hidden(B_127,k1_tops_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_315])).

tff(c_330,plain,(
    ! [A_128,B_129] :
      ( '#skF_2'('#skF_3','#skF_1'(A_128,B_129),'#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_1'(A_128,B_129),'#skF_4'),'#skF_4')
      | ~ r1_tarski(A_128,k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_108,c_319])).

tff(c_334,plain,(
    ! [B_2] :
      ( '#skF_2'('#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),'#skF_4') = k1_xboole_0
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(resolution,[status(thm)],[c_199,c_330])).

tff(c_338,plain,(
    ! [B_130] :
      ( '#skF_2'('#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_130),'#skF_4') = k1_xboole_0
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_12,c_334])).

tff(c_30,plain,(
    ! [A_19,B_26,C_27] :
      ( m1_subset_1('#skF_2'(A_19,B_26,C_27),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ r2_hidden(B_26,k1_tops_1(A_19,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_352,plain,(
    ! [B_130] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_130),k1_tops_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_30])).

tff(c_367,plain,(
    ! [B_130] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_130),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_352])).

tff(c_383,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_355,plain,(
    ! [B_130] :
      ( v3_pre_topc(k1_xboole_0,'#skF_3')
      | ~ r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_130),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_189])).

tff(c_369,plain,(
    v3_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_34,plain,(
    ! [B_39,D_45,C_43,A_31] :
      ( k1_tops_1(B_39,D_45) = D_45
      | ~ v3_pre_topc(D_45,B_39)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0(B_39)))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_242,plain,(
    ! [C_108,A_109] :
      ( ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_245,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_242])).

tff(c_249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_245])).

tff(c_250,plain,(
    ! [B_39,D_45] :
      ( k1_tops_1(B_39,D_45) = D_45
      | ~ v3_pre_topc(D_45,B_39)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0(B_39)))
      | ~ l1_pre_topc(B_39) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_393,plain,
    ( k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v3_pre_topc(k1_xboole_0,'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_383,c_250])).

tff(c_416,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_369,c_393])).

tff(c_26,plain,(
    ! [A_19,B_26,C_27] :
      ( r1_tarski('#skF_2'(A_19,B_26,C_27),C_27)
      | ~ r2_hidden(B_26,k1_tops_1(A_19,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_444,plain,(
    ! [B_26] :
      ( r1_tarski('#skF_2'('#skF_3',B_26,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_26,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_26])).

tff(c_483,plain,(
    ! [B_139] :
      ( r1_tarski('#skF_2'('#skF_3',B_139,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_139,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_383,c_444])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    ! [A_73,B_74,B_75] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(A_73,B_75)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,(
    ! [B_76,A_77,B_78] :
      ( ~ r1_tarski(B_76,'#skF_1'(A_77,B_78))
      | ~ r1_tarski(A_77,B_76)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_116,c_18])).

tff(c_139,plain,(
    ! [A_77,B_78] :
      ( ~ r1_tarski(A_77,k1_xboole_0)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_14,c_129])).

tff(c_517,plain,(
    ! [B_142,B_143] :
      ( r1_tarski('#skF_2'('#skF_3',B_142,k1_xboole_0),B_143)
      | ~ r2_hidden(B_142,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_483,c_139])).

tff(c_24,plain,(
    ! [B_26,A_19,C_27] :
      ( r2_hidden(B_26,'#skF_2'(A_19,B_26,C_27))
      | ~ r2_hidden(B_26,k1_tops_1(A_19,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_442,plain,(
    ! [B_26] :
      ( r2_hidden(B_26,'#skF_2'('#skF_3',B_26,k1_xboole_0))
      | ~ r2_hidden(B_26,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_24])).

tff(c_462,plain,(
    ! [B_135] :
      ( r2_hidden(B_135,'#skF_2'('#skF_3',B_135,k1_xboole_0))
      | ~ r2_hidden(B_135,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_383,c_442])).

tff(c_472,plain,(
    ! [B_135] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_135,k1_xboole_0),B_135)
      | ~ r2_hidden(B_135,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_462,c_18])).

tff(c_541,plain,(
    ! [B_143] : ~ r2_hidden(B_143,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_517,c_472])).

tff(c_337,plain,(
    ! [B_2] :
      ( '#skF_2'('#skF_3','#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),'#skF_4') = k1_xboole_0
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_12,c_334])).

tff(c_200,plain,(
    ! [B_97,A_98,C_99] :
      ( r2_hidden(B_97,'#skF_2'(A_98,B_97,C_99))
      | ~ r2_hidden(B_97,k1_tops_1(A_98,C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_561,plain,(
    ! [A_145,C_146,B_147] :
      ( r2_hidden('#skF_1'(k1_tops_1(A_145,C_146),B_147),'#skF_2'(A_145,'#skF_1'(k1_tops_1(A_145,C_146),B_147),C_146))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | r1_tarski(k1_tops_1(A_145,C_146),B_147) ) ),
    inference(resolution,[status(thm)],[c_6,c_200])).

tff(c_577,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2)
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_561])).

tff(c_586,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_2),k1_xboole_0)
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_577])).

tff(c_589,plain,(
    ! [B_148] : r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_148) ),
    inference(negUnitSimplification,[status(thm)],[c_541,c_586])).

tff(c_16,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ r1_tarski(A_9,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_608,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_589,c_16])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_608])).

tff(c_622,plain,(
    ! [B_149] :
      ( ~ r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_149),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_149) ) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_637,plain,(
    ! [B_150] : r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_150) ),
    inference(resolution,[status(thm)],[c_6,c_622])).

tff(c_656,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_637,c_16])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_656])).

tff(c_670,plain,(
    ! [B_151] :
      ( ~ r2_hidden('#skF_1'(k1_tops_1('#skF_3','#skF_4'),B_151),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_151) ) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_674,plain,(
    ! [B_2] :
      ( ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),k1_tops_1('#skF_3','#skF_4'))
      | r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_2) ) ),
    inference(resolution,[status(thm)],[c_108,c_670])).

tff(c_685,plain,(
    ! [B_152] : r1_tarski(k1_tops_1('#skF_3','#skF_4'),B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_674])).

tff(c_704,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_685,c_16])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_704])).

tff(c_716,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_717,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_734,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_48])).

tff(c_52,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_738,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_52])).

tff(c_810,plain,(
    ! [B_175,A_176] :
      ( v2_tops_1(B_175,A_176)
      | k1_tops_1(A_176,B_175) != k1_xboole_0
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_813,plain,
    ( v2_tops_1('#skF_5','#skF_3')
    | k1_tops_1('#skF_3','#skF_5') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_738,c_810])).

tff(c_819,plain,
    ( v2_tops_1('#skF_5','#skF_3')
    | k1_tops_1('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_813])).

tff(c_823,plain,(
    k1_tops_1('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_819])).

tff(c_50,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_732,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_50])).

tff(c_824,plain,(
    ! [A_177,B_178] :
      ( k1_tops_1(A_177,B_178) = k1_xboole_0
      | ~ v2_tops_1(B_178,A_177)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_830,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_824])).

tff(c_836,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_717,c_830])).

tff(c_1231,plain,(
    ! [A_243,B_244,C_245] :
      ( r1_tarski(k1_tops_1(A_243,B_244),k1_tops_1(A_243,C_245))
      | ~ r1_tarski(B_244,C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1243,plain,(
    ! [B_244] :
      ( r1_tarski(k1_tops_1('#skF_3',B_244),k1_xboole_0)
      | ~ r1_tarski(B_244,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_836,c_1231])).

tff(c_1251,plain,(
    ! [B_246] :
      ( r1_tarski(k1_tops_1('#skF_3',B_246),k1_xboole_0)
      | ~ r1_tarski(B_246,'#skF_4')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1243])).

tff(c_1258,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),k1_xboole_0)
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_738,c_1251])).

tff(c_1267,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_1258])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1278,plain,
    ( k1_tops_1('#skF_3','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1267,c_8])).

tff(c_1287,plain,(
    k1_tops_1('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1278])).

tff(c_1289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_1287])).

tff(c_1291,plain,(
    k1_tops_1('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_2149,plain,(
    ! [C_361,A_362] :
      ( ~ m1_subset_1(C_361,k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_2152,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_738,c_2149])).

tff(c_2159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2152])).

tff(c_2221,plain,(
    ! [B_367,D_368] :
      ( k1_tops_1(B_367,D_368) = D_368
      | ~ v3_pre_topc(D_368,B_367)
      | ~ m1_subset_1(D_368,k1_zfmisc_1(u1_struct_0(B_367)))
      | ~ l1_pre_topc(B_367) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2227,plain,
    ( k1_tops_1('#skF_3','#skF_5') = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_738,c_2221])).

tff(c_2234,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_734,c_1291,c_2227])).

tff(c_2236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_716,c_2234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:28:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.78  
% 4.28/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.78  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.59/1.78  
% 4.59/1.78  %Foreground sorts:
% 4.59/1.78  
% 4.59/1.78  
% 4.59/1.78  %Background operators:
% 4.59/1.78  
% 4.59/1.78  
% 4.59/1.78  %Foreground operators:
% 4.59/1.78  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.59/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.59/1.78  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.59/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.59/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.59/1.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.59/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.59/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.59/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.59/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.59/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.59/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.78  
% 4.69/1.81  tff(f_128, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.69/1.81  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.69/1.81  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.69/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.69/1.81  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 4.69/1.81  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 4.69/1.81  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.69/1.81  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.69/1.81  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.69/1.81  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 4.69/1.81  tff(c_46, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_68, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 4.69/1.81  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_152, plain, (![B_81, A_82]: (v2_tops_1(B_81, A_82) | k1_tops_1(A_82, B_81)!=k1_xboole_0 | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.69/1.81  tff(c_155, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_152])).
% 4.69/1.81  tff(c_158, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_155])).
% 4.69/1.81  tff(c_159, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_158])).
% 4.69/1.81  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.69/1.81  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.81  tff(c_105, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.81  tff(c_108, plain, (![A_1, B_2, B_69]: (r2_hidden('#skF_1'(A_1, B_2), B_69) | ~r1_tarski(A_1, B_69) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_105])).
% 4.69/1.81  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_191, plain, (![A_94, B_95, C_96]: (r1_tarski('#skF_2'(A_94, B_95, C_96), C_96) | ~r2_hidden(B_95, k1_tops_1(A_94, C_96)) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_199, plain, (![A_94, C_96, B_2]: (r1_tarski('#skF_2'(A_94, '#skF_1'(k1_tops_1(A_94, C_96), B_2), C_96), C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | r1_tarski(k1_tops_1(A_94, C_96), B_2))), inference(resolution, [status(thm)], [c_6, c_191])).
% 4.69/1.81  tff(c_184, plain, (![A_90, B_91, C_92]: (v3_pre_topc('#skF_2'(A_90, B_91, C_92), A_90) | ~r2_hidden(B_91, k1_tops_1(A_90, C_92)) | ~m1_subset_1(C_92, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_186, plain, (![B_91]: (v3_pre_topc('#skF_2'('#skF_3', B_91, '#skF_4'), '#skF_3') | ~r2_hidden(B_91, k1_tops_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_184])).
% 4.69/1.81  tff(c_189, plain, (![B_91]: (v3_pre_topc('#skF_2'('#skF_3', B_91, '#skF_4'), '#skF_3') | ~r2_hidden(B_91, k1_tops_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_186])).
% 4.69/1.81  tff(c_216, plain, (![A_103, B_104, C_105]: (m1_subset_1('#skF_2'(A_103, B_104, C_105), k1_zfmisc_1(u1_struct_0(A_103))) | ~r2_hidden(B_104, k1_tops_1(A_103, C_105)) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_64, plain, (![C_56]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_56 | ~v3_pre_topc(C_56, '#skF_3') | ~r1_tarski(C_56, '#skF_4') | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_168, plain, (![C_56]: (k1_xboole_0=C_56 | ~v3_pre_topc(C_56, '#skF_3') | ~r1_tarski(C_56, '#skF_4') | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_64])).
% 4.69/1.81  tff(c_222, plain, (![B_104, C_105]: ('#skF_2'('#skF_3', B_104, C_105)=k1_xboole_0 | ~v3_pre_topc('#skF_2'('#skF_3', B_104, C_105), '#skF_3') | ~r1_tarski('#skF_2'('#skF_3', B_104, C_105), '#skF_4') | ~r2_hidden(B_104, k1_tops_1('#skF_3', C_105)) | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_216, c_168])).
% 4.69/1.81  tff(c_313, plain, (![B_125, C_126]: ('#skF_2'('#skF_3', B_125, C_126)=k1_xboole_0 | ~v3_pre_topc('#skF_2'('#skF_3', B_125, C_126), '#skF_3') | ~r1_tarski('#skF_2'('#skF_3', B_125, C_126), '#skF_4') | ~r2_hidden(B_125, k1_tops_1('#skF_3', C_126)) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_222])).
% 4.69/1.81  tff(c_315, plain, (![B_91]: ('#skF_2'('#skF_3', B_91, '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2'('#skF_3', B_91, '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(B_91, k1_tops_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_189, c_313])).
% 4.69/1.81  tff(c_319, plain, (![B_127]: ('#skF_2'('#skF_3', B_127, '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2'('#skF_3', B_127, '#skF_4'), '#skF_4') | ~r2_hidden(B_127, k1_tops_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_315])).
% 4.69/1.81  tff(c_330, plain, (![A_128, B_129]: ('#skF_2'('#skF_3', '#skF_1'(A_128, B_129), '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2'('#skF_3', '#skF_1'(A_128, B_129), '#skF_4'), '#skF_4') | ~r1_tarski(A_128, k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_108, c_319])).
% 4.69/1.81  tff(c_334, plain, (![B_2]: ('#skF_2'('#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(resolution, [status(thm)], [c_199, c_330])).
% 4.69/1.81  tff(c_338, plain, (![B_130]: ('#skF_2'('#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_130), '#skF_4')=k1_xboole_0 | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_130))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_12, c_334])).
% 4.69/1.81  tff(c_30, plain, (![A_19, B_26, C_27]: (m1_subset_1('#skF_2'(A_19, B_26, C_27), k1_zfmisc_1(u1_struct_0(A_19))) | ~r2_hidden(B_26, k1_tops_1(A_19, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_352, plain, (![B_130]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_130), k1_tops_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_130))), inference(superposition, [status(thm), theory('equality')], [c_338, c_30])).
% 4.69/1.81  tff(c_367, plain, (![B_130]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_130), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_130))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_352])).
% 4.69/1.81  tff(c_383, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_367])).
% 4.69/1.81  tff(c_355, plain, (![B_130]: (v3_pre_topc(k1_xboole_0, '#skF_3') | ~r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_130), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_130))), inference(superposition, [status(thm), theory('equality')], [c_338, c_189])).
% 4.69/1.81  tff(c_369, plain, (v3_pre_topc(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_355])).
% 4.69/1.81  tff(c_34, plain, (![B_39, D_45, C_43, A_31]: (k1_tops_1(B_39, D_45)=D_45 | ~v3_pre_topc(D_45, B_39) | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0(B_39))) | ~m1_subset_1(C_43, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(B_39) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.69/1.81  tff(c_242, plain, (![C_108, A_109]: (~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109))), inference(splitLeft, [status(thm)], [c_34])).
% 4.69/1.81  tff(c_245, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_242])).
% 4.69/1.81  tff(c_249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_245])).
% 4.69/1.81  tff(c_250, plain, (![B_39, D_45]: (k1_tops_1(B_39, D_45)=D_45 | ~v3_pre_topc(D_45, B_39) | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0(B_39))) | ~l1_pre_topc(B_39))), inference(splitRight, [status(thm)], [c_34])).
% 4.69/1.81  tff(c_393, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v3_pre_topc(k1_xboole_0, '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_383, c_250])).
% 4.69/1.81  tff(c_416, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_369, c_393])).
% 4.69/1.81  tff(c_26, plain, (![A_19, B_26, C_27]: (r1_tarski('#skF_2'(A_19, B_26, C_27), C_27) | ~r2_hidden(B_26, k1_tops_1(A_19, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_444, plain, (![B_26]: (r1_tarski('#skF_2'('#skF_3', B_26, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_26, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_416, c_26])).
% 4.69/1.81  tff(c_483, plain, (![B_139]: (r1_tarski('#skF_2'('#skF_3', B_139, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_139, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_383, c_444])).
% 4.69/1.81  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/1.81  tff(c_116, plain, (![A_73, B_74, B_75]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(A_73, B_75) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_6, c_105])).
% 4.69/1.81  tff(c_18, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.69/1.81  tff(c_129, plain, (![B_76, A_77, B_78]: (~r1_tarski(B_76, '#skF_1'(A_77, B_78)) | ~r1_tarski(A_77, B_76) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_116, c_18])).
% 4.69/1.81  tff(c_139, plain, (![A_77, B_78]: (~r1_tarski(A_77, k1_xboole_0) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_14, c_129])).
% 4.69/1.81  tff(c_517, plain, (![B_142, B_143]: (r1_tarski('#skF_2'('#skF_3', B_142, k1_xboole_0), B_143) | ~r2_hidden(B_142, k1_xboole_0))), inference(resolution, [status(thm)], [c_483, c_139])).
% 4.69/1.81  tff(c_24, plain, (![B_26, A_19, C_27]: (r2_hidden(B_26, '#skF_2'(A_19, B_26, C_27)) | ~r2_hidden(B_26, k1_tops_1(A_19, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_442, plain, (![B_26]: (r2_hidden(B_26, '#skF_2'('#skF_3', B_26, k1_xboole_0)) | ~r2_hidden(B_26, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_416, c_24])).
% 4.69/1.81  tff(c_462, plain, (![B_135]: (r2_hidden(B_135, '#skF_2'('#skF_3', B_135, k1_xboole_0)) | ~r2_hidden(B_135, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_383, c_442])).
% 4.69/1.81  tff(c_472, plain, (![B_135]: (~r1_tarski('#skF_2'('#skF_3', B_135, k1_xboole_0), B_135) | ~r2_hidden(B_135, k1_xboole_0))), inference(resolution, [status(thm)], [c_462, c_18])).
% 4.69/1.81  tff(c_541, plain, (![B_143]: (~r2_hidden(B_143, k1_xboole_0))), inference(resolution, [status(thm)], [c_517, c_472])).
% 4.69/1.81  tff(c_337, plain, (![B_2]: ('#skF_2'('#skF_3', '#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), '#skF_4')=k1_xboole_0 | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_12, c_334])).
% 4.69/1.81  tff(c_200, plain, (![B_97, A_98, C_99]: (r2_hidden(B_97, '#skF_2'(A_98, B_97, C_99)) | ~r2_hidden(B_97, k1_tops_1(A_98, C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.81  tff(c_561, plain, (![A_145, C_146, B_147]: (r2_hidden('#skF_1'(k1_tops_1(A_145, C_146), B_147), '#skF_2'(A_145, '#skF_1'(k1_tops_1(A_145, C_146), B_147), C_146)) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | r1_tarski(k1_tops_1(A_145, C_146), B_147))), inference(resolution, [status(thm)], [c_6, c_200])).
% 4.69/1.81  tff(c_577, plain, (![B_2]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(superposition, [status(thm), theory('equality')], [c_337, c_561])).
% 4.69/1.81  tff(c_586, plain, (![B_2]: (r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_2), k1_xboole_0) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_577])).
% 4.69/1.81  tff(c_589, plain, (![B_148]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_148))), inference(negUnitSimplification, [status(thm)], [c_541, c_586])).
% 4.69/1.81  tff(c_16, plain, (![A_9]: (k1_xboole_0=A_9 | ~r1_tarski(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.69/1.81  tff(c_608, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_589, c_16])).
% 4.69/1.81  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_608])).
% 4.69/1.81  tff(c_622, plain, (![B_149]: (~r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_149), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_149))), inference(splitRight, [status(thm)], [c_367])).
% 4.69/1.81  tff(c_637, plain, (![B_150]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_150))), inference(resolution, [status(thm)], [c_6, c_622])).
% 4.69/1.81  tff(c_656, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_637, c_16])).
% 4.69/1.81  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_656])).
% 4.69/1.81  tff(c_670, plain, (![B_151]: (~r2_hidden('#skF_1'(k1_tops_1('#skF_3', '#skF_4'), B_151), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_151))), inference(splitRight, [status(thm)], [c_355])).
% 4.69/1.81  tff(c_674, plain, (![B_2]: (~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), k1_tops_1('#skF_3', '#skF_4')) | r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_2))), inference(resolution, [status(thm)], [c_108, c_670])).
% 4.69/1.81  tff(c_685, plain, (![B_152]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), B_152))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_674])).
% 4.69/1.81  tff(c_704, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_685, c_16])).
% 4.69/1.81  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_704])).
% 4.69/1.81  tff(c_716, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 4.69/1.81  tff(c_717, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 4.69/1.81  tff(c_48, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_734, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_48])).
% 4.69/1.81  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_738, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_52])).
% 4.69/1.81  tff(c_810, plain, (![B_175, A_176]: (v2_tops_1(B_175, A_176) | k1_tops_1(A_176, B_175)!=k1_xboole_0 | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.69/1.81  tff(c_813, plain, (v2_tops_1('#skF_5', '#skF_3') | k1_tops_1('#skF_3', '#skF_5')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_738, c_810])).
% 4.69/1.81  tff(c_819, plain, (v2_tops_1('#skF_5', '#skF_3') | k1_tops_1('#skF_3', '#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_813])).
% 4.69/1.81  tff(c_823, plain, (k1_tops_1('#skF_3', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_819])).
% 4.69/1.81  tff(c_50, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.69/1.81  tff(c_732, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_50])).
% 4.69/1.81  tff(c_824, plain, (![A_177, B_178]: (k1_tops_1(A_177, B_178)=k1_xboole_0 | ~v2_tops_1(B_178, A_177) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.69/1.81  tff(c_830, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_824])).
% 4.69/1.81  tff(c_836, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_717, c_830])).
% 4.69/1.81  tff(c_1231, plain, (![A_243, B_244, C_245]: (r1_tarski(k1_tops_1(A_243, B_244), k1_tops_1(A_243, C_245)) | ~r1_tarski(B_244, C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(u1_struct_0(A_243))) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_243))) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.81  tff(c_1243, plain, (![B_244]: (r1_tarski(k1_tops_1('#skF_3', B_244), k1_xboole_0) | ~r1_tarski(B_244, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_836, c_1231])).
% 4.69/1.81  tff(c_1251, plain, (![B_246]: (r1_tarski(k1_tops_1('#skF_3', B_246), k1_xboole_0) | ~r1_tarski(B_246, '#skF_4') | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1243])).
% 4.69/1.81  tff(c_1258, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), k1_xboole_0) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_738, c_1251])).
% 4.69/1.81  tff(c_1267, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_732, c_1258])).
% 4.69/1.81  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.69/1.81  tff(c_1278, plain, (k1_tops_1('#skF_3', '#skF_5')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_1267, c_8])).
% 4.69/1.81  tff(c_1287, plain, (k1_tops_1('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1278])).
% 4.69/1.81  tff(c_1289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_823, c_1287])).
% 4.69/1.81  tff(c_1291, plain, (k1_tops_1('#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_819])).
% 4.69/1.81  tff(c_2149, plain, (![C_361, A_362]: (~m1_subset_1(C_361, k1_zfmisc_1(u1_struct_0(A_362))) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362))), inference(splitLeft, [status(thm)], [c_34])).
% 4.69/1.81  tff(c_2152, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_738, c_2149])).
% 4.69/1.81  tff(c_2159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2152])).
% 4.69/1.81  tff(c_2221, plain, (![B_367, D_368]: (k1_tops_1(B_367, D_368)=D_368 | ~v3_pre_topc(D_368, B_367) | ~m1_subset_1(D_368, k1_zfmisc_1(u1_struct_0(B_367))) | ~l1_pre_topc(B_367))), inference(splitRight, [status(thm)], [c_34])).
% 4.69/1.81  tff(c_2227, plain, (k1_tops_1('#skF_3', '#skF_5')='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_738, c_2221])).
% 4.69/1.81  tff(c_2234, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_734, c_1291, c_2227])).
% 4.69/1.81  tff(c_2236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_716, c_2234])).
% 4.69/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.81  
% 4.69/1.81  Inference rules
% 4.69/1.81  ----------------------
% 4.69/1.81  #Ref     : 0
% 4.69/1.81  #Sup     : 447
% 4.69/1.81  #Fact    : 0
% 4.69/1.81  #Define  : 0
% 4.69/1.81  #Split   : 14
% 4.69/1.81  #Chain   : 0
% 4.69/1.81  #Close   : 0
% 4.69/1.81  
% 4.69/1.81  Ordering : KBO
% 4.69/1.81  
% 4.69/1.81  Simplification rules
% 4.69/1.81  ----------------------
% 4.69/1.81  #Subsume      : 154
% 4.69/1.81  #Demod        : 245
% 4.69/1.81  #Tautology    : 87
% 4.69/1.81  #SimpNegUnit  : 11
% 4.69/1.81  #BackRed      : 0
% 4.69/1.81  
% 4.69/1.81  #Partial instantiations: 0
% 4.69/1.81  #Strategies tried      : 1
% 4.69/1.81  
% 4.69/1.81  Timing (in seconds)
% 4.69/1.81  ----------------------
% 4.69/1.81  Preprocessing        : 0.33
% 4.69/1.81  Parsing              : 0.17
% 4.69/1.81  CNF conversion       : 0.03
% 4.69/1.81  Main loop            : 0.70
% 4.69/1.81  Inferencing          : 0.24
% 4.69/1.81  Reduction            : 0.20
% 4.69/1.81  Demodulation         : 0.13
% 4.69/1.81  BG Simplification    : 0.03
% 4.69/1.81  Subsumption          : 0.18
% 4.69/1.81  Abstraction          : 0.03
% 4.69/1.81  MUC search           : 0.00
% 4.69/1.81  Cooper               : 0.00
% 4.69/1.81  Total                : 1.09
% 4.69/1.81  Index Insertion      : 0.00
% 4.69/1.81  Index Deletion       : 0.00
% 4.69/1.81  Index Matching       : 0.00
% 4.69/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
