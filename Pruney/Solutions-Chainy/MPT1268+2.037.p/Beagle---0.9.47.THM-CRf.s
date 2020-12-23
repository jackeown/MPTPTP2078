%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:51 EST 2020

% Result     : Theorem 5.58s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 277 expanded)
%              Number of leaves         :   33 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  236 ( 791 expanded)
%              Number of equality atoms :   28 (  87 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_setfam_1,type,(
    r2_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_95,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,B)
            & ! [D] :
                ~ ( r2_hidden(D,A)
                  & r1_tarski(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_setfam_1)).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ v2_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_66,plain,(
    ~ v2_tops_1('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_327,plain,(
    ! [B_106,A_107] :
      ( v2_tops_1(B_106,A_107)
      | k1_tops_1(A_107,B_106) != k1_xboole_0
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_334,plain,
    ( v2_tops_1('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != k1_xboole_0
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_327])).

tff(c_338,plain,
    ( v2_tops_1('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_334])).

tff(c_339,plain,(
    k1_tops_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_338])).

tff(c_138,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tops_1(A_76,B_77),B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,
    ( r1_tarski(k1_tops_1('#skF_5','#skF_6'),'#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_138])).

tff(c_147,plain,(
    r1_tarski(k1_tops_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_143])).

tff(c_44,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_541,plain,(
    ! [A_132,B_133] :
      ( v3_pre_topc(k1_tops_1(A_132,B_133),A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_546,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_541])).

tff(c_550,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_546])).

tff(c_81,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_102,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(B_67,C_66)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_89,c_102])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [C_50] :
      ( v2_tops_1('#skF_6','#skF_5')
      | k1_xboole_0 = C_50
      | ~ v3_pre_topc(C_50,'#skF_5')
      | ~ r1_tarski(C_50,'#skF_6')
      | ~ m1_subset_1(C_50,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_163,plain,(
    ! [C_81] :
      ( k1_xboole_0 = C_81
      | ~ v3_pre_topc(C_81,'#skF_5')
      | ~ r1_tarski(C_81,'#skF_6')
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_64])).

tff(c_455,plain,(
    ! [A_125] :
      ( k1_xboole_0 = A_125
      | ~ v3_pre_topc(A_125,'#skF_5')
      | ~ r1_tarski(A_125,'#skF_6')
      | ~ r1_tarski(A_125,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_18,c_163])).

tff(c_481,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v3_pre_topc(A_65,'#skF_5')
      | ~ r1_tarski(A_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_107,c_455])).

tff(c_553,plain,
    ( k1_tops_1('#skF_5','#skF_6') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_550,c_481])).

tff(c_556,plain,(
    k1_tops_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_553])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_556])).

tff(c_559,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_560,plain,(
    v2_tops_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ v2_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_570,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_48])).

tff(c_50,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | ~ v2_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_568,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_50])).

tff(c_52,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ v2_tops_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_589,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_52])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_699,plain,(
    ! [A_167,B_168] :
      ( r1_tarski(k1_tops_1(A_167,B_168),B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_837,plain,(
    ! [A_176,A_177] :
      ( r1_tarski(k1_tops_1(A_176,A_177),A_177)
      | ~ l1_pre_topc(A_176)
      | ~ r1_tarski(A_177,u1_struct_0(A_176)) ) ),
    inference(resolution,[status(thm)],[c_18,c_699])).

tff(c_606,plain,(
    ! [A_147,C_148,B_149] :
      ( r1_tarski(A_147,C_148)
      | ~ r1_tarski(B_149,C_148)
      | ~ r1_tarski(A_147,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_618,plain,(
    ! [A_147,A_6] :
      ( r1_tarski(A_147,A_6)
      | ~ r1_tarski(A_147,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_606])).

tff(c_860,plain,(
    ! [A_176,A_6] :
      ( r1_tarski(k1_tops_1(A_176,k1_xboole_0),A_6)
      | ~ l1_pre_topc(A_176)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_176)) ) ),
    inference(resolution,[status(thm)],[c_837,c_618])).

tff(c_902,plain,(
    ! [A_180,A_181] :
      ( r1_tarski(k1_tops_1(A_180,k1_xboole_0),A_181)
      | ~ l1_pre_topc(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_860])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_562,plain,(
    ! [B_135,A_136] :
      ( ~ r1_tarski(B_135,A_136)
      | ~ r2_hidden(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_566,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_562])).

tff(c_957,plain,(
    ! [A_182] :
      ( k1_tops_1(A_182,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_902,c_566])).

tff(c_961,plain,(
    k1_tops_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_957])).

tff(c_1198,plain,(
    ! [A_217,B_218,C_219] :
      ( r1_tarski('#skF_4'(A_217,B_218,C_219),C_219)
      | ~ r2_hidden(B_218,k1_tops_1(A_217,C_219))
      | ~ m1_subset_1(C_219,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1202,plain,(
    ! [B_218] :
      ( r1_tarski('#skF_4'('#skF_5',B_218,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_218,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_1198])).

tff(c_1215,plain,(
    ! [B_218] :
      ( r1_tarski('#skF_4'('#skF_5',B_218,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_218,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1202])).

tff(c_1247,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1215])).

tff(c_1250,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_18,c_1247])).

tff(c_1254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1250])).

tff(c_1284,plain,(
    ! [B_224] :
      ( r1_tarski('#skF_4'('#skF_5',B_224,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_224,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1215])).

tff(c_1301,plain,(
    ! [B_225,A_226] :
      ( r1_tarski('#skF_4'('#skF_5',B_225,k1_xboole_0),A_226)
      | ~ r2_hidden(B_225,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1284,c_618])).

tff(c_594,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_2'(A_142,B_143),B_143)
      | r2_setfam_1(A_142,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_598,plain,(
    ! [B_143,A_142] :
      ( ~ r1_tarski(B_143,'#skF_2'(A_142,B_143))
      | r2_setfam_1(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_594,c_20])).

tff(c_1361,plain,(
    ! [A_142,B_225] :
      ( r2_setfam_1(A_142,'#skF_4'('#skF_5',B_225,k1_xboole_0))
      | ~ r2_hidden(B_225,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1301,c_598])).

tff(c_1256,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1215])).

tff(c_1506,plain,(
    ! [B_241,A_242,C_243] :
      ( r2_hidden(B_241,'#skF_4'(A_242,B_241,C_243))
      | ~ r2_hidden(B_241,k1_tops_1(A_242,C_243))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1510,plain,(
    ! [B_241] :
      ( r2_hidden(B_241,'#skF_4'('#skF_5',B_241,k1_xboole_0))
      | ~ r2_hidden(B_241,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_961,c_1506])).

tff(c_1563,plain,(
    ! [B_247] :
      ( r2_hidden(B_247,'#skF_4'('#skF_5',B_247,k1_xboole_0))
      | ~ r2_hidden(B_247,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1256,c_1510])).

tff(c_694,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_hidden('#skF_3'(A_164,B_165,C_166),A_164)
      | ~ r2_hidden(C_166,B_165)
      | ~ r2_setfam_1(A_164,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1060,plain,(
    ! [A_196,B_197,C_198] :
      ( ~ r1_tarski(A_196,'#skF_3'(A_196,B_197,C_198))
      | ~ r2_hidden(C_198,B_197)
      | ~ r2_setfam_1(A_196,B_197) ) ),
    inference(resolution,[status(thm)],[c_694,c_20])).

tff(c_1070,plain,(
    ! [C_198,B_197] :
      ( ~ r2_hidden(C_198,B_197)
      | ~ r2_setfam_1(k1_xboole_0,B_197) ) ),
    inference(resolution,[status(thm)],[c_6,c_1060])).

tff(c_1578,plain,(
    ! [B_248] :
      ( ~ r2_setfam_1(k1_xboole_0,'#skF_4'('#skF_5',B_248,k1_xboole_0))
      | ~ r2_hidden(B_248,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1563,c_1070])).

tff(c_1586,plain,(
    ! [B_225] : ~ r2_hidden(B_225,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1361,c_1578])).

tff(c_1009,plain,(
    ! [A_191,B_192] :
      ( k1_tops_1(A_191,B_192) = k1_xboole_0
      | ~ v2_tops_1(B_192,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1019,plain,
    ( k1_tops_1('#skF_5','#skF_6') = k1_xboole_0
    | ~ v2_tops_1('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1009])).

tff(c_1027,plain,(
    k1_tops_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_560,c_1019])).

tff(c_1656,plain,(
    ! [B_258,A_259,C_260,D_261] :
      ( r2_hidden(B_258,k1_tops_1(A_259,C_260))
      | ~ r2_hidden(B_258,D_261)
      | ~ r1_tarski(D_261,C_260)
      | ~ v3_pre_topc(D_261,A_259)
      | ~ m1_subset_1(D_261,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_subset_1(C_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4360,plain,(
    ! [A_502,A_503,C_504] :
      ( r2_hidden('#skF_1'(A_502),k1_tops_1(A_503,C_504))
      | ~ r1_tarski(A_502,C_504)
      | ~ v3_pre_topc(A_502,A_503)
      | ~ m1_subset_1(A_502,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ m1_subset_1(C_504,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | k1_xboole_0 = A_502 ) ),
    inference(resolution,[status(thm)],[c_2,c_1656])).

tff(c_4388,plain,(
    ! [A_502] :
      ( r2_hidden('#skF_1'(A_502),k1_xboole_0)
      | ~ r1_tarski(A_502,'#skF_6')
      | ~ v3_pre_topc(A_502,'#skF_5')
      | ~ m1_subset_1(A_502,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | k1_xboole_0 = A_502 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_4360])).

tff(c_4406,plain,(
    ! [A_502] :
      ( r2_hidden('#skF_1'(A_502),k1_xboole_0)
      | ~ r1_tarski(A_502,'#skF_6')
      | ~ v3_pre_topc(A_502,'#skF_5')
      | ~ m1_subset_1(A_502,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | k1_xboole_0 = A_502 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_4388])).

tff(c_4411,plain,(
    ! [A_505] :
      ( ~ r1_tarski(A_505,'#skF_6')
      | ~ v3_pre_topc(A_505,'#skF_5')
      | ~ m1_subset_1(A_505,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | k1_xboole_0 = A_505 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1586,c_4406])).

tff(c_4421,plain,
    ( ~ r1_tarski('#skF_7','#skF_6')
    | ~ v3_pre_topc('#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_589,c_4411])).

tff(c_4438,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_568,c_4421])).

tff(c_4440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_4438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.58/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.08  
% 5.58/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.08  %$ v3_pre_topc > v2_tops_1 > r2_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 5.58/2.08  
% 5.58/2.08  %Foreground sorts:
% 5.58/2.08  
% 5.58/2.08  
% 5.58/2.08  %Background operators:
% 5.58/2.08  
% 5.58/2.08  
% 5.58/2.08  %Foreground operators:
% 5.58/2.08  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.58/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.58/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.58/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.58/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.58/2.08  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.58/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.58/2.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.58/2.08  tff('#skF_7', type, '#skF_7': $i).
% 5.58/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.58/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.58/2.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.58/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.58/2.08  tff(r2_setfam_1, type, r2_setfam_1: ($i * $i) > $o).
% 5.58/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.58/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.58/2.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.58/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.58/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.58/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.58/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.58/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.58/2.08  
% 5.58/2.10  tff(f_123, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 5.58/2.10  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 5.58/2.10  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.58/2.10  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.58/2.10  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.58/2.10  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.58/2.10  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.58/2.10  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.58/2.10  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.58/2.10  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 5.58/2.10  tff(f_53, axiom, (![A, B]: (r2_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, A) & r1_tarski(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_setfam_1)).
% 5.58/2.10  tff(c_46, plain, (k1_xboole_0!='#skF_7' | ~v2_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_66, plain, (~v2_tops_1('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 5.58/2.10  tff(c_42, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_327, plain, (![B_106, A_107]: (v2_tops_1(B_106, A_107) | k1_tops_1(A_107, B_106)!=k1_xboole_0 | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.58/2.10  tff(c_334, plain, (v2_tops_1('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!=k1_xboole_0 | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_327])).
% 5.58/2.10  tff(c_338, plain, (v2_tops_1('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_334])).
% 5.58/2.10  tff(c_339, plain, (k1_tops_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_66, c_338])).
% 5.58/2.10  tff(c_138, plain, (![A_76, B_77]: (r1_tarski(k1_tops_1(A_76, B_77), B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.58/2.10  tff(c_143, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_6'), '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_138])).
% 5.58/2.10  tff(c_147, plain, (r1_tarski(k1_tops_1('#skF_5', '#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_143])).
% 5.58/2.10  tff(c_44, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_541, plain, (![A_132, B_133]: (v3_pre_topc(k1_tops_1(A_132, B_133), A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.58/2.10  tff(c_546, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_541])).
% 5.58/2.10  tff(c_550, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_546])).
% 5.58/2.10  tff(c_81, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.58/2.10  tff(c_89, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_81])).
% 5.58/2.10  tff(c_102, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(B_67, C_66) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.58/2.10  tff(c_107, plain, (![A_65]: (r1_tarski(A_65, u1_struct_0('#skF_5')) | ~r1_tarski(A_65, '#skF_6'))), inference(resolution, [status(thm)], [c_89, c_102])).
% 5.58/2.10  tff(c_18, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.58/2.10  tff(c_64, plain, (![C_50]: (v2_tops_1('#skF_6', '#skF_5') | k1_xboole_0=C_50 | ~v3_pre_topc(C_50, '#skF_5') | ~r1_tarski(C_50, '#skF_6') | ~m1_subset_1(C_50, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_163, plain, (![C_81]: (k1_xboole_0=C_81 | ~v3_pre_topc(C_81, '#skF_5') | ~r1_tarski(C_81, '#skF_6') | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_64])).
% 5.58/2.10  tff(c_455, plain, (![A_125]: (k1_xboole_0=A_125 | ~v3_pre_topc(A_125, '#skF_5') | ~r1_tarski(A_125, '#skF_6') | ~r1_tarski(A_125, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_18, c_163])).
% 5.58/2.10  tff(c_481, plain, (![A_65]: (k1_xboole_0=A_65 | ~v3_pre_topc(A_65, '#skF_5') | ~r1_tarski(A_65, '#skF_6'))), inference(resolution, [status(thm)], [c_107, c_455])).
% 5.58/2.10  tff(c_553, plain, (k1_tops_1('#skF_5', '#skF_6')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_550, c_481])).
% 5.58/2.10  tff(c_556, plain, (k1_tops_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_147, c_553])).
% 5.58/2.10  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_339, c_556])).
% 5.58/2.10  tff(c_559, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_46])).
% 5.58/2.10  tff(c_560, plain, (v2_tops_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 5.58/2.10  tff(c_48, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~v2_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_570, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_48])).
% 5.58/2.10  tff(c_50, plain, (r1_tarski('#skF_7', '#skF_6') | ~v2_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_568, plain, (r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_50])).
% 5.58/2.10  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v2_tops_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.58/2.10  tff(c_589, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_52])).
% 5.58/2.10  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.58/2.10  tff(c_699, plain, (![A_167, B_168]: (r1_tarski(k1_tops_1(A_167, B_168), B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.58/2.10  tff(c_837, plain, (![A_176, A_177]: (r1_tarski(k1_tops_1(A_176, A_177), A_177) | ~l1_pre_topc(A_176) | ~r1_tarski(A_177, u1_struct_0(A_176)))), inference(resolution, [status(thm)], [c_18, c_699])).
% 5.58/2.10  tff(c_606, plain, (![A_147, C_148, B_149]: (r1_tarski(A_147, C_148) | ~r1_tarski(B_149, C_148) | ~r1_tarski(A_147, B_149))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.58/2.10  tff(c_618, plain, (![A_147, A_6]: (r1_tarski(A_147, A_6) | ~r1_tarski(A_147, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_606])).
% 5.58/2.10  tff(c_860, plain, (![A_176, A_6]: (r1_tarski(k1_tops_1(A_176, k1_xboole_0), A_6) | ~l1_pre_topc(A_176) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_176)))), inference(resolution, [status(thm)], [c_837, c_618])).
% 5.58/2.10  tff(c_902, plain, (![A_180, A_181]: (r1_tarski(k1_tops_1(A_180, k1_xboole_0), A_181) | ~l1_pre_topc(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_860])).
% 5.58/2.10  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.58/2.10  tff(c_562, plain, (![B_135, A_136]: (~r1_tarski(B_135, A_136) | ~r2_hidden(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.58/2.10  tff(c_566, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_562])).
% 5.58/2.10  tff(c_957, plain, (![A_182]: (k1_tops_1(A_182, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_902, c_566])).
% 5.58/2.10  tff(c_961, plain, (k1_tops_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_957])).
% 5.58/2.10  tff(c_1198, plain, (![A_217, B_218, C_219]: (r1_tarski('#skF_4'(A_217, B_218, C_219), C_219) | ~r2_hidden(B_218, k1_tops_1(A_217, C_219)) | ~m1_subset_1(C_219, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.58/2.10  tff(c_1202, plain, (![B_218]: (r1_tarski('#skF_4'('#skF_5', B_218, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_218, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_961, c_1198])).
% 5.58/2.10  tff(c_1215, plain, (![B_218]: (r1_tarski('#skF_4'('#skF_5', B_218, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_218, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1202])).
% 5.58/2.10  tff(c_1247, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_1215])).
% 5.58/2.10  tff(c_1250, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_1247])).
% 5.58/2.10  tff(c_1254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1250])).
% 5.58/2.10  tff(c_1284, plain, (![B_224]: (r1_tarski('#skF_4'('#skF_5', B_224, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_224, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1215])).
% 5.58/2.10  tff(c_1301, plain, (![B_225, A_226]: (r1_tarski('#skF_4'('#skF_5', B_225, k1_xboole_0), A_226) | ~r2_hidden(B_225, k1_xboole_0))), inference(resolution, [status(thm)], [c_1284, c_618])).
% 5.58/2.10  tff(c_594, plain, (![A_142, B_143]: (r2_hidden('#skF_2'(A_142, B_143), B_143) | r2_setfam_1(A_142, B_143))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.58/2.10  tff(c_20, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.58/2.10  tff(c_598, plain, (![B_143, A_142]: (~r1_tarski(B_143, '#skF_2'(A_142, B_143)) | r2_setfam_1(A_142, B_143))), inference(resolution, [status(thm)], [c_594, c_20])).
% 5.58/2.10  tff(c_1361, plain, (![A_142, B_225]: (r2_setfam_1(A_142, '#skF_4'('#skF_5', B_225, k1_xboole_0)) | ~r2_hidden(B_225, k1_xboole_0))), inference(resolution, [status(thm)], [c_1301, c_598])).
% 5.58/2.10  tff(c_1256, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1215])).
% 5.58/2.10  tff(c_1506, plain, (![B_241, A_242, C_243]: (r2_hidden(B_241, '#skF_4'(A_242, B_241, C_243)) | ~r2_hidden(B_241, k1_tops_1(A_242, C_243)) | ~m1_subset_1(C_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.58/2.10  tff(c_1510, plain, (![B_241]: (r2_hidden(B_241, '#skF_4'('#skF_5', B_241, k1_xboole_0)) | ~r2_hidden(B_241, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_961, c_1506])).
% 5.58/2.10  tff(c_1563, plain, (![B_247]: (r2_hidden(B_247, '#skF_4'('#skF_5', B_247, k1_xboole_0)) | ~r2_hidden(B_247, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1256, c_1510])).
% 5.58/2.10  tff(c_694, plain, (![A_164, B_165, C_166]: (r2_hidden('#skF_3'(A_164, B_165, C_166), A_164) | ~r2_hidden(C_166, B_165) | ~r2_setfam_1(A_164, B_165))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.58/2.10  tff(c_1060, plain, (![A_196, B_197, C_198]: (~r1_tarski(A_196, '#skF_3'(A_196, B_197, C_198)) | ~r2_hidden(C_198, B_197) | ~r2_setfam_1(A_196, B_197))), inference(resolution, [status(thm)], [c_694, c_20])).
% 5.58/2.10  tff(c_1070, plain, (![C_198, B_197]: (~r2_hidden(C_198, B_197) | ~r2_setfam_1(k1_xboole_0, B_197))), inference(resolution, [status(thm)], [c_6, c_1060])).
% 5.58/2.10  tff(c_1578, plain, (![B_248]: (~r2_setfam_1(k1_xboole_0, '#skF_4'('#skF_5', B_248, k1_xboole_0)) | ~r2_hidden(B_248, k1_xboole_0))), inference(resolution, [status(thm)], [c_1563, c_1070])).
% 5.58/2.10  tff(c_1586, plain, (![B_225]: (~r2_hidden(B_225, k1_xboole_0))), inference(resolution, [status(thm)], [c_1361, c_1578])).
% 5.58/2.10  tff(c_1009, plain, (![A_191, B_192]: (k1_tops_1(A_191, B_192)=k1_xboole_0 | ~v2_tops_1(B_192, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.58/2.10  tff(c_1019, plain, (k1_tops_1('#skF_5', '#skF_6')=k1_xboole_0 | ~v2_tops_1('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1009])).
% 5.58/2.10  tff(c_1027, plain, (k1_tops_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_560, c_1019])).
% 5.58/2.10  tff(c_1656, plain, (![B_258, A_259, C_260, D_261]: (r2_hidden(B_258, k1_tops_1(A_259, C_260)) | ~r2_hidden(B_258, D_261) | ~r1_tarski(D_261, C_260) | ~v3_pre_topc(D_261, A_259) | ~m1_subset_1(D_261, k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_subset_1(C_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.58/2.10  tff(c_4360, plain, (![A_502, A_503, C_504]: (r2_hidden('#skF_1'(A_502), k1_tops_1(A_503, C_504)) | ~r1_tarski(A_502, C_504) | ~v3_pre_topc(A_502, A_503) | ~m1_subset_1(A_502, k1_zfmisc_1(u1_struct_0(A_503))) | ~m1_subset_1(C_504, k1_zfmisc_1(u1_struct_0(A_503))) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | k1_xboole_0=A_502)), inference(resolution, [status(thm)], [c_2, c_1656])).
% 5.58/2.10  tff(c_4388, plain, (![A_502]: (r2_hidden('#skF_1'(A_502), k1_xboole_0) | ~r1_tarski(A_502, '#skF_6') | ~v3_pre_topc(A_502, '#skF_5') | ~m1_subset_1(A_502, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | k1_xboole_0=A_502)), inference(superposition, [status(thm), theory('equality')], [c_1027, c_4360])).
% 5.58/2.10  tff(c_4406, plain, (![A_502]: (r2_hidden('#skF_1'(A_502), k1_xboole_0) | ~r1_tarski(A_502, '#skF_6') | ~v3_pre_topc(A_502, '#skF_5') | ~m1_subset_1(A_502, k1_zfmisc_1(u1_struct_0('#skF_5'))) | k1_xboole_0=A_502)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_4388])).
% 5.58/2.10  tff(c_4411, plain, (![A_505]: (~r1_tarski(A_505, '#skF_6') | ~v3_pre_topc(A_505, '#skF_5') | ~m1_subset_1(A_505, k1_zfmisc_1(u1_struct_0('#skF_5'))) | k1_xboole_0=A_505)), inference(negUnitSimplification, [status(thm)], [c_1586, c_4406])).
% 5.58/2.10  tff(c_4421, plain, (~r1_tarski('#skF_7', '#skF_6') | ~v3_pre_topc('#skF_7', '#skF_5') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_589, c_4411])).
% 5.58/2.10  tff(c_4438, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_570, c_568, c_4421])).
% 5.58/2.10  tff(c_4440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_4438])).
% 5.58/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.10  
% 5.58/2.10  Inference rules
% 5.58/2.10  ----------------------
% 5.58/2.10  #Ref     : 0
% 5.58/2.10  #Sup     : 945
% 5.58/2.10  #Fact    : 0
% 5.58/2.10  #Define  : 0
% 5.58/2.10  #Split   : 15
% 5.58/2.10  #Chain   : 0
% 5.58/2.10  #Close   : 0
% 5.58/2.10  
% 5.58/2.10  Ordering : KBO
% 5.58/2.10  
% 5.58/2.10  Simplification rules
% 5.58/2.10  ----------------------
% 5.58/2.10  #Subsume      : 392
% 5.58/2.10  #Demod        : 512
% 5.58/2.10  #Tautology    : 172
% 5.58/2.10  #SimpNegUnit  : 13
% 5.58/2.10  #BackRed      : 2
% 5.58/2.10  
% 5.58/2.10  #Partial instantiations: 0
% 5.58/2.10  #Strategies tried      : 1
% 5.58/2.10  
% 5.58/2.10  Timing (in seconds)
% 5.58/2.10  ----------------------
% 5.58/2.11  Preprocessing        : 0.31
% 5.58/2.11  Parsing              : 0.16
% 5.58/2.11  CNF conversion       : 0.02
% 5.58/2.11  Main loop            : 1.02
% 5.58/2.11  Inferencing          : 0.36
% 5.58/2.11  Reduction            : 0.30
% 5.58/2.11  Demodulation         : 0.20
% 5.58/2.11  BG Simplification    : 0.03
% 5.58/2.11  Subsumption          : 0.27
% 5.58/2.11  Abstraction          : 0.04
% 5.58/2.11  MUC search           : 0.00
% 5.58/2.11  Cooper               : 0.00
% 5.58/2.11  Total                : 1.37
% 5.58/2.11  Index Insertion      : 0.00
% 5.58/2.11  Index Deletion       : 0.00
% 5.58/2.11  Index Matching       : 0.00
% 5.58/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
