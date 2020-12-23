%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:21 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 200 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 500 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_122,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [C_19] :
      ( ~ r2_hidden(C_19,'#skF_5')
      | ~ m1_subset_1(C_19,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_142,plain,(
    ! [B_38] :
      ( ~ m1_subset_1(B_38,'#skF_4')
      | ~ m1_subset_1(B_38,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_122,c_32])).

tff(c_148,plain,(
    ! [B_40] :
      ( ~ m1_subset_1(B_40,'#skF_4')
      | ~ m1_subset_1(B_40,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_158,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,'#skF_4')
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_148])).

tff(c_166,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_301,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_2'(A_61,B_62),B_62)
      | r2_hidden('#skF_3'(A_61,B_62),A_61)
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    ! [A_22,B_23] : ~ r2_hidden(A_22,k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_59])).

tff(c_345,plain,(
    ! [B_63] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_63),B_63)
      | k1_xboole_0 = B_63 ) ),
    inference(resolution,[status(thm)],[c_301,c_62])).

tff(c_357,plain,
    ( ~ m1_subset_1('#skF_2'(k1_xboole_0,'#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_345,c_32])).

tff(c_370,plain,(
    ~ m1_subset_1('#skF_2'(k1_xboole_0,'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_357])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ r2_hidden(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_367,plain,(
    ! [B_63] :
      ( m1_subset_1('#skF_2'(k1_xboole_0,B_63),B_63)
      | v1_xboole_0(B_63)
      | k1_xboole_0 = B_63 ) ),
    inference(resolution,[status(thm)],[c_345,c_22])).

tff(c_91,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(B_31)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [C_28] :
      ( ~ r2_hidden(C_28,'#skF_5')
      | ~ m1_subset_1(C_28,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_84,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_99,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_84])).

tff(c_100,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_159,plain,(
    ! [C_41,A_42,B_43] :
      ( r2_hidden(C_41,A_42)
      | ~ r2_hidden(C_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_776,plain,(
    ! [B_90,A_91,A_92] :
      ( r2_hidden(B_90,A_91)
      | ~ m1_subset_1(A_92,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_90,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_24,c_159])).

tff(c_795,plain,(
    ! [B_90] :
      ( r2_hidden(B_90,'#skF_4')
      | ~ m1_subset_1(B_90,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_776])).

tff(c_805,plain,(
    ! [B_93] :
      ( r2_hidden(B_93,'#skF_4')
      | ~ m1_subset_1(B_93,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_795])).

tff(c_817,plain,(
    ! [B_93] :
      ( m1_subset_1(B_93,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_93,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_805,c_22])).

tff(c_828,plain,(
    ! [B_94] :
      ( m1_subset_1(B_94,'#skF_4')
      | ~ m1_subset_1(B_94,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_817])).

tff(c_840,plain,
    ( m1_subset_1('#skF_2'(k1_xboole_0,'#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_367,c_828])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_166,c_370,c_840])).

tff(c_860,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1008,plain,(
    ! [A_113,B_114] :
      ( r2_hidden('#skF_2'(A_113,B_114),B_114)
      | r2_hidden('#skF_3'(A_113,B_114),A_113)
      | B_114 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1052,plain,(
    ! [A_115,B_116] :
      ( ~ v1_xboole_0(A_115)
      | r2_hidden('#skF_2'(A_115,B_116),B_116)
      | B_116 = A_115 ) ),
    inference(resolution,[status(thm)],[c_1008,c_2])).

tff(c_1078,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0(A_117)
      | k1_xboole_0 = A_117 ) ),
    inference(resolution,[status(thm)],[c_1052,c_62])).

tff(c_1087,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_860,c_1078])).

tff(c_1096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1087])).

tff(c_1098,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_1099,plain,(
    ! [B_118,A_119] :
      ( r2_hidden(B_118,A_119)
      | ~ m1_subset_1(B_118,A_119)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1115,plain,(
    ! [B_118] :
      ( ~ m1_subset_1(B_118,'#skF_4')
      | ~ m1_subset_1(B_118,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1099,c_32])).

tff(c_1146,plain,(
    ! [B_125] :
      ( ~ m1_subset_1(B_125,'#skF_4')
      | ~ m1_subset_1(B_125,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_1115])).

tff(c_1156,plain,(
    ! [B_13] :
      ( ~ m1_subset_1(B_13,'#skF_4')
      | ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_1146])).

tff(c_1164,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1156])).

tff(c_1157,plain,(
    ! [C_126,A_127,B_128] :
      ( r2_hidden(C_126,A_127)
      | ~ r2_hidden(C_126,B_128)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1185,plain,(
    ! [A_133,A_134] :
      ( r2_hidden('#skF_1'(A_133),A_134)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(A_134))
      | v1_xboole_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_4,c_1157])).

tff(c_1224,plain,(
    ! [A_136,A_137] :
      ( ~ v1_xboole_0(A_136)
      | ~ m1_subset_1(A_137,k1_zfmisc_1(A_136))
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_1185,c_2])).

tff(c_1235,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1224])).

tff(c_1240,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1235])).

tff(c_1242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1164,c_1240])).

tff(c_1251,plain,(
    ! [B_140] :
      ( ~ m1_subset_1(B_140,'#skF_4')
      | ~ v1_xboole_0(B_140) ) ),
    inference(splitRight,[status(thm)],[c_1156])).

tff(c_1259,plain,(
    ! [B_13] :
      ( ~ v1_xboole_0(B_13)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1251])).

tff(c_1264,plain,(
    ! [B_13] : ~ v1_xboole_0(B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1098,c_1259])).

tff(c_1244,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1156])).

tff(c_1273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1264,c_1244])).

tff(c_1274,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1115])).

tff(c_1408,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158,B_159),B_159)
      | r2_hidden('#skF_3'(A_158,B_159),A_158)
      | B_159 = A_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1445,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_160),B_160)
      | k1_xboole_0 = B_160 ) ),
    inference(resolution,[status(thm)],[c_1408,c_62])).

tff(c_1470,plain,(
    ! [B_161] :
      ( ~ v1_xboole_0(B_161)
      | k1_xboole_0 = B_161 ) ),
    inference(resolution,[status(thm)],[c_1445,c_2])).

tff(c_1479,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1274,c_1470])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.52  
% 3.22/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.52  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.22/1.52  
% 3.22/1.52  %Foreground sorts:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Background operators:
% 3.22/1.52  
% 3.22/1.52  
% 3.22/1.52  %Foreground operators:
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.22/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.22/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.22/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.52  
% 3.35/1.54  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 3.35/1.54  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.35/1.54  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.35/1.54  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.35/1.54  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.35/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.35/1.54  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.35/1.54  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.54  tff(c_26, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~v1_xboole_0(B_13) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_122, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_32, plain, (![C_19]: (~r2_hidden(C_19, '#skF_5') | ~m1_subset_1(C_19, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.54  tff(c_142, plain, (![B_38]: (~m1_subset_1(B_38, '#skF_4') | ~m1_subset_1(B_38, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_122, c_32])).
% 3.35/1.54  tff(c_148, plain, (![B_40]: (~m1_subset_1(B_40, '#skF_4') | ~m1_subset_1(B_40, '#skF_5'))), inference(splitLeft, [status(thm)], [c_142])).
% 3.35/1.54  tff(c_158, plain, (![B_13]: (~m1_subset_1(B_13, '#skF_4') | ~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_148])).
% 3.35/1.54  tff(c_166, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_158])).
% 3.35/1.54  tff(c_301, plain, (![A_61, B_62]: (r2_hidden('#skF_2'(A_61, B_62), B_62) | r2_hidden('#skF_3'(A_61, B_62), A_61) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.54  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.35/1.54  tff(c_59, plain, (![A_22, B_23]: (~r2_hidden(A_22, k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.54  tff(c_62, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_59])).
% 3.35/1.54  tff(c_345, plain, (![B_63]: (r2_hidden('#skF_2'(k1_xboole_0, B_63), B_63) | k1_xboole_0=B_63)), inference(resolution, [status(thm)], [c_301, c_62])).
% 3.35/1.54  tff(c_357, plain, (~m1_subset_1('#skF_2'(k1_xboole_0, '#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_345, c_32])).
% 3.35/1.54  tff(c_370, plain, (~m1_subset_1('#skF_2'(k1_xboole_0, '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_357])).
% 3.35/1.54  tff(c_22, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~r2_hidden(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_367, plain, (![B_63]: (m1_subset_1('#skF_2'(k1_xboole_0, B_63), B_63) | v1_xboole_0(B_63) | k1_xboole_0=B_63)), inference(resolution, [status(thm)], [c_345, c_22])).
% 3.35/1.54  tff(c_91, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~v1_xboole_0(B_31) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.54  tff(c_78, plain, (![C_28]: (~r2_hidden(C_28, '#skF_5') | ~m1_subset_1(C_28, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.54  tff(c_83, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_78])).
% 3.35/1.54  tff(c_84, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_83])).
% 3.35/1.54  tff(c_99, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_91, c_84])).
% 3.35/1.54  tff(c_100, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_99])).
% 3.35/1.54  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.54  tff(c_24, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_159, plain, (![C_41, A_42, B_43]: (r2_hidden(C_41, A_42) | ~r2_hidden(C_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.35/1.54  tff(c_776, plain, (![B_90, A_91, A_92]: (r2_hidden(B_90, A_91) | ~m1_subset_1(A_92, k1_zfmisc_1(A_91)) | ~m1_subset_1(B_90, A_92) | v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_24, c_159])).
% 3.35/1.54  tff(c_795, plain, (![B_90]: (r2_hidden(B_90, '#skF_4') | ~m1_subset_1(B_90, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_776])).
% 3.35/1.54  tff(c_805, plain, (![B_93]: (r2_hidden(B_93, '#skF_4') | ~m1_subset_1(B_93, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_166, c_795])).
% 3.35/1.54  tff(c_817, plain, (![B_93]: (m1_subset_1(B_93, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_93, '#skF_5'))), inference(resolution, [status(thm)], [c_805, c_22])).
% 3.35/1.54  tff(c_828, plain, (![B_94]: (m1_subset_1(B_94, '#skF_4') | ~m1_subset_1(B_94, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_100, c_817])).
% 3.35/1.54  tff(c_840, plain, (m1_subset_1('#skF_2'(k1_xboole_0, '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_367, c_828])).
% 3.35/1.54  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_166, c_370, c_840])).
% 3.35/1.54  tff(c_860, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_158])).
% 3.35/1.54  tff(c_1008, plain, (![A_113, B_114]: (r2_hidden('#skF_2'(A_113, B_114), B_114) | r2_hidden('#skF_3'(A_113, B_114), A_113) | B_114=A_113)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.54  tff(c_1052, plain, (![A_115, B_116]: (~v1_xboole_0(A_115) | r2_hidden('#skF_2'(A_115, B_116), B_116) | B_116=A_115)), inference(resolution, [status(thm)], [c_1008, c_2])).
% 3.35/1.54  tff(c_1078, plain, (![A_117]: (~v1_xboole_0(A_117) | k1_xboole_0=A_117)), inference(resolution, [status(thm)], [c_1052, c_62])).
% 3.35/1.54  tff(c_1087, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_860, c_1078])).
% 3.35/1.54  tff(c_1096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1087])).
% 3.35/1.54  tff(c_1098, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_99])).
% 3.35/1.54  tff(c_1099, plain, (![B_118, A_119]: (r2_hidden(B_118, A_119) | ~m1_subset_1(B_118, A_119) | v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.35/1.54  tff(c_1115, plain, (![B_118]: (~m1_subset_1(B_118, '#skF_4') | ~m1_subset_1(B_118, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1099, c_32])).
% 3.35/1.54  tff(c_1146, plain, (![B_125]: (~m1_subset_1(B_125, '#skF_4') | ~m1_subset_1(B_125, '#skF_5'))), inference(splitLeft, [status(thm)], [c_1115])).
% 3.35/1.54  tff(c_1156, plain, (![B_13]: (~m1_subset_1(B_13, '#skF_4') | ~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_1146])).
% 3.35/1.54  tff(c_1164, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1156])).
% 3.35/1.54  tff(c_1157, plain, (![C_126, A_127, B_128]: (r2_hidden(C_126, A_127) | ~r2_hidden(C_126, B_128) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.35/1.54  tff(c_1185, plain, (![A_133, A_134]: (r2_hidden('#skF_1'(A_133), A_134) | ~m1_subset_1(A_133, k1_zfmisc_1(A_134)) | v1_xboole_0(A_133))), inference(resolution, [status(thm)], [c_4, c_1157])).
% 3.35/1.54  tff(c_1224, plain, (![A_136, A_137]: (~v1_xboole_0(A_136) | ~m1_subset_1(A_137, k1_zfmisc_1(A_136)) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_1185, c_2])).
% 3.35/1.54  tff(c_1235, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_1224])).
% 3.35/1.54  tff(c_1240, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1235])).
% 3.35/1.54  tff(c_1242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1164, c_1240])).
% 3.35/1.54  tff(c_1251, plain, (![B_140]: (~m1_subset_1(B_140, '#skF_4') | ~v1_xboole_0(B_140))), inference(splitRight, [status(thm)], [c_1156])).
% 3.35/1.54  tff(c_1259, plain, (![B_13]: (~v1_xboole_0(B_13) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1251])).
% 3.35/1.54  tff(c_1264, plain, (![B_13]: (~v1_xboole_0(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_1098, c_1259])).
% 3.35/1.54  tff(c_1244, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1156])).
% 3.35/1.54  tff(c_1273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1264, c_1244])).
% 3.35/1.54  tff(c_1274, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1115])).
% 3.35/1.54  tff(c_1408, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158, B_159), B_159) | r2_hidden('#skF_3'(A_158, B_159), A_158) | B_159=A_158)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.54  tff(c_1445, plain, (![B_160]: (r2_hidden('#skF_2'(k1_xboole_0, B_160), B_160) | k1_xboole_0=B_160)), inference(resolution, [status(thm)], [c_1408, c_62])).
% 3.35/1.54  tff(c_1470, plain, (![B_161]: (~v1_xboole_0(B_161) | k1_xboole_0=B_161)), inference(resolution, [status(thm)], [c_1445, c_2])).
% 3.35/1.54  tff(c_1479, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1274, c_1470])).
% 3.35/1.54  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1479])).
% 3.35/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.54  
% 3.35/1.54  Inference rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Ref     : 0
% 3.35/1.54  #Sup     : 292
% 3.35/1.54  #Fact    : 0
% 3.35/1.54  #Define  : 0
% 3.35/1.54  #Split   : 11
% 3.35/1.54  #Chain   : 0
% 3.35/1.54  #Close   : 0
% 3.35/1.54  
% 3.35/1.54  Ordering : KBO
% 3.35/1.54  
% 3.35/1.54  Simplification rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Subsume      : 62
% 3.35/1.54  #Demod        : 55
% 3.35/1.54  #Tautology    : 71
% 3.35/1.54  #SimpNegUnit  : 29
% 3.35/1.54  #BackRed      : 9
% 3.35/1.54  
% 3.35/1.54  #Partial instantiations: 0
% 3.35/1.54  #Strategies tried      : 1
% 3.35/1.54  
% 3.35/1.54  Timing (in seconds)
% 3.35/1.54  ----------------------
% 3.35/1.54  Preprocessing        : 0.30
% 3.35/1.54  Parsing              : 0.16
% 3.35/1.54  CNF conversion       : 0.02
% 3.35/1.54  Main loop            : 0.46
% 3.35/1.54  Inferencing          : 0.18
% 3.35/1.54  Reduction            : 0.11
% 3.35/1.54  Demodulation         : 0.07
% 3.35/1.54  BG Simplification    : 0.03
% 3.35/1.54  Subsumption          : 0.10
% 3.35/1.54  Abstraction          : 0.02
% 3.35/1.54  MUC search           : 0.00
% 3.35/1.54  Cooper               : 0.00
% 3.35/1.54  Total                : 0.80
% 3.35/1.54  Index Insertion      : 0.00
% 3.35/1.54  Index Deletion       : 0.00
% 3.35/1.54  Index Matching       : 0.00
% 3.35/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
