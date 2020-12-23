%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:52 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 723 expanded)
%              Number of leaves         :   30 ( 253 expanded)
%              Depth                    :   15
%              Number of atoms          :  383 (2255 expanded)
%              Number of equality atoms :   46 ( 237 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_86,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1254,plain,(
    ! [A_160,B_161] :
      ( r1_tarski(k1_tops_1(A_160,B_161),B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1259,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1254])).

tff(c_1263,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1259])).

tff(c_84,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(resolution,[status(thm)],[c_84,c_4])).

tff(c_74,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_1214,plain,(
    ! [A_152,C_153,B_154] :
      ( r1_tarski(A_152,C_153)
      | ~ r1_tarski(B_154,C_153)
      | ~ r1_tarski(A_152,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1235,plain,(
    ! [A_157] :
      ( r1_tarski(A_157,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_157,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_1214])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1238,plain,(
    ! [A_6,A_157] :
      ( r1_tarski(A_6,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_6,A_157)
      | ~ r1_tarski(A_157,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1235,c_8])).

tff(c_1265,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1263,c_1238])).

tff(c_1270,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1265])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_153,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_tops_1(A_69,B_70),B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_158,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_153])).

tff(c_162,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_158])).

tff(c_113,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(A_61,C_62)
      | ~ r1_tarski(B_63,C_62)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_134,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_113])).

tff(c_137,plain,(
    ! [A_6,A_66] :
      ( r1_tarski(A_6,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_6,A_66)
      | ~ r1_tarski(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_8])).

tff(c_164,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_137])).

tff(c_169,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_164])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_253,plain,(
    ! [A_79,B_80] :
      ( v3_pre_topc(k1_tops_1(A_79,B_80),A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_258,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_253])).

tff(c_262,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_258])).

tff(c_54,plain,(
    ! [C_42] :
      ( k1_xboole_0 != '#skF_5'
      | k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,(
    ! [C_42] :
      ( r1_tarski('#skF_5','#skF_4')
      | k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_308,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [C_42] :
      ( v3_pre_topc('#skF_5','#skF_3')
      | k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_191,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_310,plain,
    ( r1_tarski('#skF_5',u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_308,c_137])).

tff(c_315,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_310])).

tff(c_62,plain,(
    ! [C_42] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_451,plain,(
    ! [C_95] :
      ( k1_xboole_0 = C_95
      | ~ v3_pre_topc(C_95,'#skF_3')
      | ~ r1_tarski(C_95,'#skF_4')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62])).

tff(c_476,plain,(
    ! [A_97] :
      ( k1_xboole_0 = A_97
      | ~ v3_pre_topc(A_97,'#skF_3')
      | ~ r1_tarski(A_97,'#skF_4')
      | ~ r1_tarski(A_97,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_451])).

tff(c_482,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_315,c_476])).

tff(c_511,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_191,c_482])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_511])).

tff(c_516,plain,(
    ! [C_98] :
      ( k1_xboole_0 = C_98
      | ~ v3_pre_topc(C_98,'#skF_3')
      | ~ r1_tarski(C_98,'#skF_4')
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_573,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | ~ v3_pre_topc(A_105,'#skF_3')
      | ~ r1_tarski(A_105,'#skF_4')
      | ~ r1_tarski(A_105,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_516])).

tff(c_584,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_573])).

tff(c_603,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_262,c_584])).

tff(c_642,plain,(
    ! [B_107,A_108] :
      ( v2_tops_1(B_107,A_108)
      | k1_tops_1(A_108,B_107) != k1_xboole_0
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_649,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_642])).

tff(c_653,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_603,c_649])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_653])).

tff(c_749,plain,(
    ! [C_114] :
      ( k1_xboole_0 = C_114
      | ~ v3_pre_topc(C_114,'#skF_3')
      | ~ r1_tarski(C_114,'#skF_4')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_931,plain,(
    ! [A_132] :
      ( k1_xboole_0 = A_132
      | ~ v3_pre_topc(A_132,'#skF_3')
      | ~ r1_tarski(A_132,'#skF_4')
      | ~ r1_tarski(A_132,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_749])).

tff(c_948,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_931])).

tff(c_972,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_948])).

tff(c_983,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_972])).

tff(c_1070,plain,(
    ! [A_142,B_143] :
      ( v3_pre_topc(k1_tops_1(A_142,B_143),A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1075,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1070])).

tff(c_1079,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1075])).

tff(c_1081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_983,c_1079])).

tff(c_1082,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_972])).

tff(c_1170,plain,(
    ! [B_148,A_149] :
      ( v2_tops_1(B_148,A_149)
      | k1_tops_1(A_149,B_148) != k1_xboole_0
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1177,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1170])).

tff(c_1181,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1082,c_1177])).

tff(c_1183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1181])).

tff(c_1185,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1184,plain,(
    ! [C_42] :
      ( k1_xboole_0 = C_42
      | ~ v3_pre_topc(C_42,'#skF_3')
      | ~ r1_tarski(C_42,'#skF_4')
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1387,plain,(
    ! [C_169] :
      ( C_169 = '#skF_5'
      | ~ v3_pre_topc(C_169,'#skF_3')
      | ~ r1_tarski(C_169,'#skF_4')
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1184])).

tff(c_1458,plain,(
    ! [A_179] :
      ( A_179 = '#skF_5'
      | ~ v3_pre_topc(A_179,'#skF_3')
      | ~ r1_tarski(A_179,'#skF_4')
      | ~ r1_tarski(A_179,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_1387])).

tff(c_1469,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1270,c_1458])).

tff(c_1488,plain,
    ( k1_tops_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1469])).

tff(c_1506,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1488])).

tff(c_1563,plain,(
    ! [A_187,B_188] :
      ( v3_pre_topc(k1_tops_1(A_187,B_188),A_187)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1568,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1563])).

tff(c_1572,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1568])).

tff(c_1574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1506,c_1572])).

tff(c_1575,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1488])).

tff(c_34,plain,(
    ! [B_34,A_32] :
      ( v2_tops_1(B_34,A_32)
      | k1_tops_1(A_32,B_34) != k1_xboole_0
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1643,plain,(
    ! [B_195,A_196] :
      ( v2_tops_1(B_195,A_196)
      | k1_tops_1(A_196,B_195) != '#skF_5'
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_34])).

tff(c_1650,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != '#skF_5'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1643])).

tff(c_1654,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1575,c_1650])).

tff(c_1656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1654])).

tff(c_1657,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1658,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1669,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1658,c_46])).

tff(c_48,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1667,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1658,c_48])).

tff(c_50,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1682,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1658,c_50])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1842,plain,(
    ! [A_232,B_233] :
      ( r1_tarski(k1_tops_1(A_232,B_233),B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2013,plain,(
    ! [A_243,A_244] :
      ( r1_tarski(k1_tops_1(A_243,A_244),A_244)
      | ~ l1_pre_topc(A_243)
      | ~ r1_tarski(A_244,u1_struct_0(A_243)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1842])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2046,plain,(
    ! [A_243] :
      ( k1_tops_1(A_243,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_243)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_243)) ) ),
    inference(resolution,[status(thm)],[c_2013,c_12])).

tff(c_2066,plain,(
    ! [A_245] :
      ( k1_tops_1(A_245,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2046])).

tff(c_2070,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_2066])).

tff(c_2288,plain,(
    ! [A_266,B_267,C_268] :
      ( r1_tarski('#skF_2'(A_266,B_267,C_268),C_268)
      | ~ r2_hidden(B_267,k1_tops_1(A_266,C_268))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2290,plain,(
    ! [B_267] :
      ( r1_tarski('#skF_2'('#skF_3',B_267,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_267,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_2288])).

tff(c_2300,plain,(
    ! [B_267] :
      ( r1_tarski('#skF_2'('#skF_3',B_267,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_267,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2290])).

tff(c_2334,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2300])).

tff(c_2337,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_2334])).

tff(c_2341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2337])).

tff(c_2376,plain,(
    ! [B_271] :
      ( r1_tarski('#skF_2'('#skF_3',B_271,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_271,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_2300])).

tff(c_1712,plain,(
    ! [A_211,C_212,B_213] :
      ( r1_tarski(A_211,C_212)
      | ~ r1_tarski(B_213,C_212)
      | ~ r1_tarski(A_211,B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1727,plain,(
    ! [A_211,A_9] :
      ( r1_tarski(A_211,A_9)
      | ~ r1_tarski(A_211,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_1712])).

tff(c_2394,plain,(
    ! [B_271,A_9] :
      ( r1_tarski('#skF_2'('#skF_3',B_271,k1_xboole_0),A_9)
      | ~ r2_hidden(B_271,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2376,c_1727])).

tff(c_2343,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2300])).

tff(c_2397,plain,(
    ! [B_272,A_273,C_274] :
      ( r2_hidden(B_272,'#skF_2'(A_273,B_272,C_274))
      | ~ r2_hidden(B_272,k1_tops_1(A_273,C_274))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2399,plain,(
    ! [B_272] :
      ( r2_hidden(B_272,'#skF_2'('#skF_3',B_272,k1_xboole_0))
      | ~ r2_hidden(B_272,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_2397])).

tff(c_2455,plain,(
    ! [B_278] :
      ( r2_hidden(B_278,'#skF_2'('#skF_3',B_278,k1_xboole_0))
      | ~ r2_hidden(B_278,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2343,c_2399])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2526,plain,(
    ! [B_282] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_282,k1_xboole_0),B_282)
      | ~ r2_hidden(B_282,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2455,c_18])).

tff(c_2539,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2394,c_2526])).

tff(c_1885,plain,(
    ! [A_234,B_235] :
      ( k1_tops_1(A_234,B_235) = k1_xboole_0
      | ~ v2_tops_1(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1895,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1885])).

tff(c_1902,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1658,c_1895])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2576,plain,(
    ! [B_287,A_288,C_289,D_290] :
      ( r2_hidden(B_287,k1_tops_1(A_288,C_289))
      | ~ r2_hidden(B_287,D_290)
      | ~ r1_tarski(D_290,C_289)
      | ~ v3_pre_topc(D_290,A_288)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4007,plain,(
    ! [A_426,B_427,A_428,C_429] :
      ( r2_hidden('#skF_1'(A_426,B_427),k1_tops_1(A_428,C_429))
      | ~ r1_tarski(A_426,C_429)
      | ~ v3_pre_topc(A_426,A_428)
      | ~ m1_subset_1(A_426,k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ m1_subset_1(C_429,k1_zfmisc_1(u1_struct_0(A_428)))
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | r1_tarski(A_426,B_427) ) ),
    inference(resolution,[status(thm)],[c_6,c_2576])).

tff(c_4028,plain,(
    ! [A_426,B_427] :
      ( r2_hidden('#skF_1'(A_426,B_427),k1_xboole_0)
      | ~ r1_tarski(A_426,'#skF_4')
      | ~ v3_pre_topc(A_426,'#skF_3')
      | ~ m1_subset_1(A_426,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(A_426,B_427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_4007])).

tff(c_4039,plain,(
    ! [A_426,B_427] :
      ( r2_hidden('#skF_1'(A_426,B_427),k1_xboole_0)
      | ~ r1_tarski(A_426,'#skF_4')
      | ~ v3_pre_topc(A_426,'#skF_3')
      | ~ m1_subset_1(A_426,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_426,B_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_4028])).

tff(c_4047,plain,(
    ! [A_431,B_432] :
      ( ~ r1_tarski(A_431,'#skF_4')
      | ~ v3_pre_topc(A_431,'#skF_3')
      | ~ m1_subset_1(A_431,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_431,B_432) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2539,c_4039])).

tff(c_4054,plain,(
    ! [B_432] :
      ( ~ r1_tarski('#skF_5','#skF_4')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | r1_tarski('#skF_5',B_432) ) ),
    inference(resolution,[status(thm)],[c_1682,c_4047])).

tff(c_4068,plain,(
    ! [B_432] : r1_tarski('#skF_5',B_432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1667,c_4054])).

tff(c_1844,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1682,c_1842])).

tff(c_1852,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1844])).

tff(c_1756,plain,(
    ! [C_218,B_219,A_220] :
      ( r2_hidden(C_218,B_219)
      | ~ r2_hidden(C_218,A_220)
      | ~ r1_tarski(A_220,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1818,plain,(
    ! [A_226,B_227,B_228] :
      ( r2_hidden('#skF_1'(A_226,B_227),B_228)
      | ~ r1_tarski(A_226,B_228)
      | r1_tarski(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_6,c_1756])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2780,plain,(
    ! [A_304,B_305,B_306,B_307] :
      ( r2_hidden('#skF_1'(A_304,B_305),B_306)
      | ~ r1_tarski(B_307,B_306)
      | ~ r1_tarski(A_304,B_307)
      | r1_tarski(A_304,B_305) ) ),
    inference(resolution,[status(thm)],[c_1818,c_2])).

tff(c_2911,plain,(
    ! [A_325,B_326] :
      ( r2_hidden('#skF_1'(A_325,B_326),'#skF_5')
      | ~ r1_tarski(A_325,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_325,B_326) ) ),
    inference(resolution,[status(thm)],[c_1852,c_2780])).

tff(c_3828,plain,(
    ! [A_408,B_409,B_410] :
      ( r2_hidden('#skF_1'(A_408,B_409),B_410)
      | ~ r1_tarski('#skF_5',B_410)
      | ~ r1_tarski(A_408,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_408,B_409) ) ),
    inference(resolution,[status(thm)],[c_2911,c_2])).

tff(c_3851,plain,(
    ! [A_408,B_409] :
      ( ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(A_408,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_408,B_409) ) ),
    inference(resolution,[status(thm)],[c_3828,c_2539])).

tff(c_3911,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3851])).

tff(c_4101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4068,c_3911])).

tff(c_4103,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3851])).

tff(c_4150,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_4103,c_12])).

tff(c_4174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1657,c_4150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:49:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.10  
% 5.81/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.10  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.81/2.10  
% 5.81/2.10  %Foreground sorts:
% 5.81/2.10  
% 5.81/2.10  
% 5.81/2.10  %Background operators:
% 5.81/2.10  
% 5.81/2.10  
% 5.81/2.10  %Foreground operators:
% 5.81/2.10  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.81/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.81/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.81/2.10  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.81/2.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.81/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.81/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.81/2.10  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.81/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.81/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.81/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.81/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.81/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.81/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.10  
% 5.98/2.13  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 5.98/2.13  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 5.98/2.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.98/2.13  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.98/2.13  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.98/2.13  tff(f_61, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.98/2.13  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 5.98/2.13  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.98/2.13  tff(f_44, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.98/2.13  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 5.98/2.13  tff(f_53, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.98/2.13  tff(c_44, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_64, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.98/2.13  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_1254, plain, (![A_160, B_161]: (r1_tarski(k1_tops_1(A_160, B_161), B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.98/2.13  tff(c_1259, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1254])).
% 5.98/2.13  tff(c_1263, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1259])).
% 5.98/2.13  tff(c_84, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.98/2.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.98/2.13  tff(c_92, plain, (![A_53]: (r1_tarski(A_53, A_53))), inference(resolution, [status(thm)], [c_84, c_4])).
% 5.98/2.13  tff(c_74, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.98/2.13  tff(c_82, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 5.98/2.13  tff(c_1214, plain, (![A_152, C_153, B_154]: (r1_tarski(A_152, C_153) | ~r1_tarski(B_154, C_153) | ~r1_tarski(A_152, B_154))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.13  tff(c_1235, plain, (![A_157]: (r1_tarski(A_157, u1_struct_0('#skF_3')) | ~r1_tarski(A_157, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_1214])).
% 5.98/2.13  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.13  tff(c_1238, plain, (![A_6, A_157]: (r1_tarski(A_6, u1_struct_0('#skF_3')) | ~r1_tarski(A_6, A_157) | ~r1_tarski(A_157, '#skF_4'))), inference(resolution, [status(thm)], [c_1235, c_8])).
% 5.98/2.13  tff(c_1265, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1263, c_1238])).
% 5.98/2.13  tff(c_1270, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1265])).
% 5.98/2.13  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.98/2.13  tff(c_153, plain, (![A_69, B_70]: (r1_tarski(k1_tops_1(A_69, B_70), B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.98/2.13  tff(c_158, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_153])).
% 5.98/2.13  tff(c_162, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_158])).
% 5.98/2.13  tff(c_113, plain, (![A_61, C_62, B_63]: (r1_tarski(A_61, C_62) | ~r1_tarski(B_63, C_62) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.13  tff(c_134, plain, (![A_66]: (r1_tarski(A_66, u1_struct_0('#skF_3')) | ~r1_tarski(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_113])).
% 5.98/2.13  tff(c_137, plain, (![A_6, A_66]: (r1_tarski(A_6, u1_struct_0('#skF_3')) | ~r1_tarski(A_6, A_66) | ~r1_tarski(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_134, c_8])).
% 5.98/2.13  tff(c_164, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_162, c_137])).
% 5.98/2.13  tff(c_169, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_164])).
% 5.98/2.13  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_253, plain, (![A_79, B_80]: (v3_pre_topc(k1_tops_1(A_79, B_80), A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.13  tff(c_258, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_253])).
% 5.98/2.13  tff(c_262, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_258])).
% 5.98/2.13  tff(c_54, plain, (![C_42]: (k1_xboole_0!='#skF_5' | k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_112, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_54])).
% 5.98/2.13  tff(c_58, plain, (![C_42]: (r1_tarski('#skF_5', '#skF_4') | k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_308, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 5.98/2.13  tff(c_56, plain, (![C_42]: (v3_pre_topc('#skF_5', '#skF_3') | k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_191, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 5.98/2.13  tff(c_310, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_308, c_137])).
% 5.98/2.13  tff(c_315, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_310])).
% 5.98/2.13  tff(c_62, plain, (![C_42]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_451, plain, (![C_95]: (k1_xboole_0=C_95 | ~v3_pre_topc(C_95, '#skF_3') | ~r1_tarski(C_95, '#skF_4') | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_62])).
% 5.98/2.13  tff(c_476, plain, (![A_97]: (k1_xboole_0=A_97 | ~v3_pre_topc(A_97, '#skF_3') | ~r1_tarski(A_97, '#skF_4') | ~r1_tarski(A_97, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_451])).
% 5.98/2.13  tff(c_482, plain, (k1_xboole_0='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_3') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_315, c_476])).
% 5.98/2.13  tff(c_511, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_191, c_482])).
% 5.98/2.13  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_511])).
% 5.98/2.13  tff(c_516, plain, (![C_98]: (k1_xboole_0=C_98 | ~v3_pre_topc(C_98, '#skF_3') | ~r1_tarski(C_98, '#skF_4') | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_58])).
% 5.98/2.13  tff(c_573, plain, (![A_105]: (k1_xboole_0=A_105 | ~v3_pre_topc(A_105, '#skF_3') | ~r1_tarski(A_105, '#skF_4') | ~r1_tarski(A_105, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_516])).
% 5.98/2.13  tff(c_584, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_169, c_573])).
% 5.98/2.13  tff(c_603, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_162, c_262, c_584])).
% 5.98/2.13  tff(c_642, plain, (![B_107, A_108]: (v2_tops_1(B_107, A_108) | k1_tops_1(A_108, B_107)!=k1_xboole_0 | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.98/2.13  tff(c_649, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_642])).
% 5.98/2.13  tff(c_653, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_603, c_649])).
% 5.98/2.13  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_653])).
% 5.98/2.13  tff(c_749, plain, (![C_114]: (k1_xboole_0=C_114 | ~v3_pre_topc(C_114, '#skF_3') | ~r1_tarski(C_114, '#skF_4') | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_56])).
% 5.98/2.13  tff(c_931, plain, (![A_132]: (k1_xboole_0=A_132 | ~v3_pre_topc(A_132, '#skF_3') | ~r1_tarski(A_132, '#skF_4') | ~r1_tarski(A_132, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_749])).
% 5.98/2.13  tff(c_948, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_169, c_931])).
% 5.98/2.13  tff(c_972, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_948])).
% 5.98/2.13  tff(c_983, plain, (~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_972])).
% 5.98/2.13  tff(c_1070, plain, (![A_142, B_143]: (v3_pre_topc(k1_tops_1(A_142, B_143), A_142) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.13  tff(c_1075, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1070])).
% 5.98/2.13  tff(c_1079, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1075])).
% 5.98/2.13  tff(c_1081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_983, c_1079])).
% 5.98/2.13  tff(c_1082, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_972])).
% 5.98/2.13  tff(c_1170, plain, (![B_148, A_149]: (v2_tops_1(B_148, A_149) | k1_tops_1(A_149, B_148)!=k1_xboole_0 | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.98/2.13  tff(c_1177, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1170])).
% 5.98/2.13  tff(c_1181, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1082, c_1177])).
% 5.98/2.13  tff(c_1183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1181])).
% 5.98/2.13  tff(c_1185, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 5.98/2.13  tff(c_1184, plain, (![C_42]: (k1_xboole_0=C_42 | ~v3_pre_topc(C_42, '#skF_3') | ~r1_tarski(C_42, '#skF_4') | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_54])).
% 5.98/2.13  tff(c_1387, plain, (![C_169]: (C_169='#skF_5' | ~v3_pre_topc(C_169, '#skF_3') | ~r1_tarski(C_169, '#skF_4') | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1184])).
% 5.98/2.13  tff(c_1458, plain, (![A_179]: (A_179='#skF_5' | ~v3_pre_topc(A_179, '#skF_3') | ~r1_tarski(A_179, '#skF_4') | ~r1_tarski(A_179, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_1387])).
% 5.98/2.13  tff(c_1469, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_5' | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1270, c_1458])).
% 5.98/2.13  tff(c_1488, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_5' | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1469])).
% 5.98/2.13  tff(c_1506, plain, (~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1488])).
% 5.98/2.13  tff(c_1563, plain, (![A_187, B_188]: (v3_pre_topc(k1_tops_1(A_187, B_188), A_187) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.13  tff(c_1568, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1563])).
% 5.98/2.13  tff(c_1572, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1568])).
% 5.98/2.13  tff(c_1574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1506, c_1572])).
% 5.98/2.13  tff(c_1575, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1488])).
% 5.98/2.13  tff(c_34, plain, (![B_34, A_32]: (v2_tops_1(B_34, A_32) | k1_tops_1(A_32, B_34)!=k1_xboole_0 | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.98/2.13  tff(c_1643, plain, (![B_195, A_196]: (v2_tops_1(B_195, A_196) | k1_tops_1(A_196, B_195)!='#skF_5' | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_34])).
% 5.98/2.13  tff(c_1650, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1643])).
% 5.98/2.13  tff(c_1654, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1575, c_1650])).
% 5.98/2.13  tff(c_1656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1654])).
% 5.98/2.13  tff(c_1657, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 5.98/2.13  tff(c_1658, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 5.98/2.13  tff(c_46, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_1669, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1658, c_46])).
% 5.98/2.13  tff(c_48, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_1667, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1658, c_48])).
% 5.98/2.13  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.98/2.13  tff(c_1682, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1658, c_50])).
% 5.98/2.13  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.13  tff(c_1842, plain, (![A_232, B_233]: (r1_tarski(k1_tops_1(A_232, B_233), B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.98/2.13  tff(c_2013, plain, (![A_243, A_244]: (r1_tarski(k1_tops_1(A_243, A_244), A_244) | ~l1_pre_topc(A_243) | ~r1_tarski(A_244, u1_struct_0(A_243)))), inference(resolution, [status(thm)], [c_16, c_1842])).
% 5.98/2.13  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.98/2.13  tff(c_2046, plain, (![A_243]: (k1_tops_1(A_243, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_243) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_243)))), inference(resolution, [status(thm)], [c_2013, c_12])).
% 5.98/2.13  tff(c_2066, plain, (![A_245]: (k1_tops_1(A_245, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_245))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2046])).
% 5.98/2.13  tff(c_2070, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_2066])).
% 5.98/2.13  tff(c_2288, plain, (![A_266, B_267, C_268]: (r1_tarski('#skF_2'(A_266, B_267, C_268), C_268) | ~r2_hidden(B_267, k1_tops_1(A_266, C_268)) | ~m1_subset_1(C_268, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.98/2.13  tff(c_2290, plain, (![B_267]: (r1_tarski('#skF_2'('#skF_3', B_267, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_267, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2070, c_2288])).
% 5.98/2.13  tff(c_2300, plain, (![B_267]: (r1_tarski('#skF_2'('#skF_3', B_267, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_267, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2290])).
% 5.98/2.13  tff(c_2334, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2300])).
% 5.98/2.13  tff(c_2337, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_2334])).
% 5.98/2.13  tff(c_2341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_2337])).
% 5.98/2.13  tff(c_2376, plain, (![B_271]: (r1_tarski('#skF_2'('#skF_3', B_271, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_271, k1_xboole_0))), inference(splitRight, [status(thm)], [c_2300])).
% 5.98/2.13  tff(c_1712, plain, (![A_211, C_212, B_213]: (r1_tarski(A_211, C_212) | ~r1_tarski(B_213, C_212) | ~r1_tarski(A_211, B_213))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.13  tff(c_1727, plain, (![A_211, A_9]: (r1_tarski(A_211, A_9) | ~r1_tarski(A_211, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_1712])).
% 5.98/2.13  tff(c_2394, plain, (![B_271, A_9]: (r1_tarski('#skF_2'('#skF_3', B_271, k1_xboole_0), A_9) | ~r2_hidden(B_271, k1_xboole_0))), inference(resolution, [status(thm)], [c_2376, c_1727])).
% 5.98/2.13  tff(c_2343, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2300])).
% 5.98/2.13  tff(c_2397, plain, (![B_272, A_273, C_274]: (r2_hidden(B_272, '#skF_2'(A_273, B_272, C_274)) | ~r2_hidden(B_272, k1_tops_1(A_273, C_274)) | ~m1_subset_1(C_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.98/2.13  tff(c_2399, plain, (![B_272]: (r2_hidden(B_272, '#skF_2'('#skF_3', B_272, k1_xboole_0)) | ~r2_hidden(B_272, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2070, c_2397])).
% 5.98/2.13  tff(c_2455, plain, (![B_278]: (r2_hidden(B_278, '#skF_2'('#skF_3', B_278, k1_xboole_0)) | ~r2_hidden(B_278, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2343, c_2399])).
% 5.98/2.13  tff(c_18, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.98/2.13  tff(c_2526, plain, (![B_282]: (~r1_tarski('#skF_2'('#skF_3', B_282, k1_xboole_0), B_282) | ~r2_hidden(B_282, k1_xboole_0))), inference(resolution, [status(thm)], [c_2455, c_18])).
% 5.98/2.13  tff(c_2539, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(resolution, [status(thm)], [c_2394, c_2526])).
% 5.98/2.13  tff(c_1885, plain, (![A_234, B_235]: (k1_tops_1(A_234, B_235)=k1_xboole_0 | ~v2_tops_1(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.98/2.13  tff(c_1895, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1885])).
% 5.98/2.13  tff(c_1902, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1658, c_1895])).
% 5.98/2.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.98/2.13  tff(c_2576, plain, (![B_287, A_288, C_289, D_290]: (r2_hidden(B_287, k1_tops_1(A_288, C_289)) | ~r2_hidden(B_287, D_290) | ~r1_tarski(D_290, C_289) | ~v3_pre_topc(D_290, A_288) | ~m1_subset_1(D_290, k1_zfmisc_1(u1_struct_0(A_288))) | ~m1_subset_1(C_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.98/2.13  tff(c_4007, plain, (![A_426, B_427, A_428, C_429]: (r2_hidden('#skF_1'(A_426, B_427), k1_tops_1(A_428, C_429)) | ~r1_tarski(A_426, C_429) | ~v3_pre_topc(A_426, A_428) | ~m1_subset_1(A_426, k1_zfmisc_1(u1_struct_0(A_428))) | ~m1_subset_1(C_429, k1_zfmisc_1(u1_struct_0(A_428))) | ~l1_pre_topc(A_428) | ~v2_pre_topc(A_428) | r1_tarski(A_426, B_427))), inference(resolution, [status(thm)], [c_6, c_2576])).
% 5.98/2.13  tff(c_4028, plain, (![A_426, B_427]: (r2_hidden('#skF_1'(A_426, B_427), k1_xboole_0) | ~r1_tarski(A_426, '#skF_4') | ~v3_pre_topc(A_426, '#skF_3') | ~m1_subset_1(A_426, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(A_426, B_427))), inference(superposition, [status(thm), theory('equality')], [c_1902, c_4007])).
% 5.98/2.13  tff(c_4039, plain, (![A_426, B_427]: (r2_hidden('#skF_1'(A_426, B_427), k1_xboole_0) | ~r1_tarski(A_426, '#skF_4') | ~v3_pre_topc(A_426, '#skF_3') | ~m1_subset_1(A_426, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_426, B_427))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_4028])).
% 5.98/2.13  tff(c_4047, plain, (![A_431, B_432]: (~r1_tarski(A_431, '#skF_4') | ~v3_pre_topc(A_431, '#skF_3') | ~m1_subset_1(A_431, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_431, B_432))), inference(negUnitSimplification, [status(thm)], [c_2539, c_4039])).
% 5.98/2.13  tff(c_4054, plain, (![B_432]: (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | r1_tarski('#skF_5', B_432))), inference(resolution, [status(thm)], [c_1682, c_4047])).
% 5.98/2.13  tff(c_4068, plain, (![B_432]: (r1_tarski('#skF_5', B_432))), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1667, c_4054])).
% 5.98/2.13  tff(c_1844, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1682, c_1842])).
% 5.98/2.13  tff(c_1852, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1844])).
% 5.98/2.13  tff(c_1756, plain, (![C_218, B_219, A_220]: (r2_hidden(C_218, B_219) | ~r2_hidden(C_218, A_220) | ~r1_tarski(A_220, B_219))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.98/2.13  tff(c_1818, plain, (![A_226, B_227, B_228]: (r2_hidden('#skF_1'(A_226, B_227), B_228) | ~r1_tarski(A_226, B_228) | r1_tarski(A_226, B_227))), inference(resolution, [status(thm)], [c_6, c_1756])).
% 5.98/2.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.98/2.13  tff(c_2780, plain, (![A_304, B_305, B_306, B_307]: (r2_hidden('#skF_1'(A_304, B_305), B_306) | ~r1_tarski(B_307, B_306) | ~r1_tarski(A_304, B_307) | r1_tarski(A_304, B_305))), inference(resolution, [status(thm)], [c_1818, c_2])).
% 5.98/2.13  tff(c_2911, plain, (![A_325, B_326]: (r2_hidden('#skF_1'(A_325, B_326), '#skF_5') | ~r1_tarski(A_325, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_325, B_326))), inference(resolution, [status(thm)], [c_1852, c_2780])).
% 5.98/2.13  tff(c_3828, plain, (![A_408, B_409, B_410]: (r2_hidden('#skF_1'(A_408, B_409), B_410) | ~r1_tarski('#skF_5', B_410) | ~r1_tarski(A_408, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_408, B_409))), inference(resolution, [status(thm)], [c_2911, c_2])).
% 5.98/2.13  tff(c_3851, plain, (![A_408, B_409]: (~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(A_408, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_408, B_409))), inference(resolution, [status(thm)], [c_3828, c_2539])).
% 5.98/2.13  tff(c_3911, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3851])).
% 5.98/2.13  tff(c_4101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4068, c_3911])).
% 5.98/2.13  tff(c_4103, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3851])).
% 5.98/2.13  tff(c_4150, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_4103, c_12])).
% 5.98/2.13  tff(c_4174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1657, c_4150])).
% 5.98/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.13  
% 5.98/2.13  Inference rules
% 5.98/2.13  ----------------------
% 5.98/2.13  #Ref     : 0
% 5.98/2.13  #Sup     : 872
% 5.98/2.13  #Fact    : 0
% 5.98/2.13  #Define  : 0
% 5.98/2.13  #Split   : 28
% 5.98/2.13  #Chain   : 0
% 5.98/2.13  #Close   : 0
% 5.98/2.13  
% 5.98/2.13  Ordering : KBO
% 5.98/2.13  
% 5.98/2.13  Simplification rules
% 5.98/2.13  ----------------------
% 5.98/2.13  #Subsume      : 293
% 5.98/2.13  #Demod        : 484
% 5.98/2.13  #Tautology    : 203
% 5.98/2.13  #SimpNegUnit  : 24
% 5.98/2.13  #BackRed      : 26
% 5.98/2.13  
% 5.98/2.13  #Partial instantiations: 0
% 5.98/2.13  #Strategies tried      : 1
% 5.98/2.13  
% 5.98/2.13  Timing (in seconds)
% 5.98/2.13  ----------------------
% 5.98/2.13  Preprocessing        : 0.31
% 5.98/2.13  Parsing              : 0.16
% 5.98/2.13  CNF conversion       : 0.02
% 5.98/2.13  Main loop            : 1.01
% 5.98/2.13  Inferencing          : 0.34
% 5.98/2.13  Reduction            : 0.30
% 5.98/2.13  Demodulation         : 0.20
% 5.98/2.13  BG Simplification    : 0.03
% 5.98/2.13  Subsumption          : 0.26
% 5.98/2.13  Abstraction          : 0.04
% 5.98/2.13  MUC search           : 0.00
% 5.98/2.13  Cooper               : 0.00
% 5.98/2.13  Total                : 1.38
% 5.98/2.14  Index Insertion      : 0.00
% 5.98/2.14  Index Deletion       : 0.00
% 5.98/2.14  Index Matching       : 0.00
% 5.98/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
