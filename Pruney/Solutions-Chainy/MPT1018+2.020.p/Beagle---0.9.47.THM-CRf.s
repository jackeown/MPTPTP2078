%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  122 (1261 expanded)
%              Number of leaves         :   33 ( 402 expanded)
%              Depth                    :   16
%              Number of atoms          :  232 (3453 expanded)
%              Number of equality atoms :   87 (1446 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_318,plain,(
    ! [D_77,C_78,B_79,A_80] :
      ( k1_funct_1(k2_funct_1(D_77),k1_funct_1(D_77,C_78)) = C_78
      | k1_xboole_0 = B_79
      | ~ r2_hidden(C_78,A_80)
      | ~ v2_funct_1(D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_2(D_77,A_80,B_79)
      | ~ v1_funct_1(D_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_365,plain,(
    ! [D_82,B_83] :
      ( k1_funct_1(k2_funct_1(D_82),k1_funct_1(D_82,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_83
      | ~ v2_funct_1(D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_83)))
      | ~ v1_funct_2(D_82,'#skF_1',B_83)
      | ~ v1_funct_1(D_82) ) ),
    inference(resolution,[status(thm)],[c_40,c_318])).

tff(c_370,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_365])).

tff(c_377,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_370])).

tff(c_399,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_416,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_413,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_399,c_12])).

tff(c_87,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_87])).

tff(c_96,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,
    ( k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_96])).

tff(c_122,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_492,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_122])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_492])).

tff(c_499,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_498,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_38,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_587,plain,(
    ! [D_104,B_105] :
      ( k1_funct_1(k2_funct_1(D_104),k1_funct_1(D_104,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_105
      | ~ v2_funct_1(D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_105)))
      | ~ v1_funct_2(D_104,'#skF_1',B_105)
      | ~ v1_funct_1(D_104) ) ),
    inference(resolution,[status(thm)],[c_42,c_318])).

tff(c_592,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_587])).

tff(c_599,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_498,c_38,c_592])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_36,c_599])).

tff(c_602,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_605,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_46])).

tff(c_874,plain,(
    ! [D_150,C_151,B_152,A_153] :
      ( k1_funct_1(k2_funct_1(D_150),k1_funct_1(D_150,C_151)) = C_151
      | k1_xboole_0 = B_152
      | ~ r2_hidden(C_151,A_153)
      | ~ v2_funct_1(D_150)
      | ~ m1_subset_1(D_150,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152)))
      | ~ v1_funct_2(D_150,A_153,B_152)
      | ~ v1_funct_1(D_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_940,plain,(
    ! [D_161,B_162] :
      ( k1_funct_1(k2_funct_1(D_161),k1_funct_1(D_161,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_162
      | ~ v2_funct_1(D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_162)))
      | ~ v1_funct_2(D_161,'#skF_1',B_162)
      | ~ v1_funct_1(D_161) ) ),
    inference(resolution,[status(thm)],[c_40,c_874])).

tff(c_942,plain,(
    ! [D_161] :
      ( k1_funct_1(k2_funct_1(D_161),k1_funct_1(D_161,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = '#skF_1'
      | ~ v2_funct_1(D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_2(D_161,'#skF_1','#skF_1')
      | ~ v1_funct_1(D_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_940])).

tff(c_1151,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_942])).

tff(c_619,plain,(
    ! [B_106,A_107] :
      ( k1_xboole_0 = B_106
      | k1_xboole_0 = A_107
      | k2_zfmisc_1(A_107,B_106) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_622,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_619])).

tff(c_640,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_622])).

tff(c_1170,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_640])).

tff(c_1173,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_1151,c_12])).

tff(c_1253,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1173,c_602])).

tff(c_1255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1170,c_1253])).

tff(c_2211,plain,(
    ! [D_242] :
      ( k1_funct_1(k2_funct_1(D_242),k1_funct_1(D_242,'#skF_4')) = '#skF_4'
      | ~ v2_funct_1(D_242)
      | ~ m1_subset_1(D_242,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_2(D_242,'#skF_1','#skF_1')
      | ~ v1_funct_1(D_242) ) ),
    inference(splitRight,[status(thm)],[c_942])).

tff(c_1257,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_942])).

tff(c_1061,plain,(
    ! [D_179,B_180] :
      ( k1_funct_1(k2_funct_1(D_179),k1_funct_1(D_179,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_180
      | ~ v2_funct_1(D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_180)))
      | ~ v1_funct_2(D_179,'#skF_1',B_180)
      | ~ v1_funct_1(D_179) ) ),
    inference(resolution,[status(thm)],[c_42,c_874])).

tff(c_1063,plain,(
    ! [D_179] :
      ( k1_funct_1(k2_funct_1(D_179),k1_funct_1(D_179,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = '#skF_1'
      | ~ v2_funct_1(D_179)
      | ~ m1_subset_1(D_179,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_2(D_179,'#skF_1','#skF_1')
      | ~ v1_funct_1(D_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_1061])).

tff(c_1284,plain,(
    ! [D_198] :
      ( k1_funct_1(k2_funct_1(D_198),k1_funct_1(D_198,'#skF_3')) = '#skF_3'
      | ~ v2_funct_1(D_198)
      | ~ m1_subset_1(D_198,k1_zfmisc_1('#skF_2'))
      | ~ v1_funct_2(D_198,'#skF_1','#skF_1')
      | ~ v1_funct_1(D_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1257,c_1063])).

tff(c_1310,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1284])).

tff(c_1316,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_605,c_44,c_1310])).

tff(c_2220,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2211,c_1316])).

tff(c_2246,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_605,c_44,c_2220])).

tff(c_2248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2246])).

tff(c_2250,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_2249,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_2294,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2250,c_2249])).

tff(c_2295,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2294])).

tff(c_24,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_609,plain,(
    v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_24])).

tff(c_2316,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_609])).

tff(c_2321,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_50])).

tff(c_2320,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_44])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2255,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2250,c_14])).

tff(c_2311,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_2295,c_2255])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2349,plain,(
    ! [C_250,A_251,B_252] :
      ( v4_relat_1(C_250,A_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2530,plain,(
    ! [A_279,A_280,B_281] :
      ( v4_relat_1(A_279,A_280)
      | ~ r1_tarski(A_279,k2_zfmisc_1(A_280,B_281)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2349])).

tff(c_2552,plain,(
    ! [A_280,B_281] : v4_relat_1(k2_zfmisc_1(A_280,B_281),A_280) ),
    inference(resolution,[status(thm)],[c_6,c_2530])).

tff(c_2430,plain,(
    ! [B_258,A_259] :
      ( r1_tarski(k1_relat_1(B_258),A_259)
      | ~ v4_relat_1(B_258,A_259)
      | ~ v1_relat_1(B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_2252,plain,(
    ! [A_3] :
      ( A_3 = '#skF_2'
      | ~ r1_tarski(A_3,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2250,c_2250,c_104])).

tff(c_2399,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_2295,c_2252])).

tff(c_2584,plain,(
    ! [B_290] :
      ( k1_relat_1(B_290) = '#skF_1'
      | ~ v4_relat_1(B_290,'#skF_1')
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_2430,c_2399])).

tff(c_2588,plain,(
    ! [B_281] :
      ( k1_relat_1(k2_zfmisc_1('#skF_1',B_281)) = '#skF_1'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_281)) ) ),
    inference(resolution,[status(thm)],[c_2552,c_2584])).

tff(c_2599,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2311,c_2588])).

tff(c_2318,plain,(
    k1_funct_1('#skF_1','#skF_3') = k1_funct_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_2295,c_38])).

tff(c_2475,plain,(
    ! [B_272,A_273] :
      ( k1_funct_1(k2_funct_1(B_272),k1_funct_1(B_272,A_273)) = A_273
      | ~ r2_hidden(A_273,k1_relat_1(B_272))
      | ~ v2_funct_1(B_272)
      | ~ v1_funct_1(B_272)
      | ~ v1_relat_1(B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2493,plain,
    ( k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_2475])).

tff(c_2497,plain,
    ( k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_4')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2316,c_2321,c_2320,c_2493])).

tff(c_2824,plain,(
    k1_funct_1(k2_funct_1('#skF_1'),k1_funct_1('#skF_1','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2599,c_2497])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( k1_funct_1(k2_funct_1(B_13),k1_funct_1(B_13,A_12)) = A_12
      | ~ r2_hidden(A_12,k1_relat_1(B_13))
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2831,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2824,c_28])).

tff(c_2838,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2316,c_2321,c_2320,c_40,c_2599,c_2831])).

tff(c_2840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2838])).

tff(c_2841,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2294])).

tff(c_2842,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2294])).

tff(c_2865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2841,c_2842])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.82  
% 4.65/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.65/1.83  
% 4.65/1.83  %Foreground sorts:
% 4.65/1.83  
% 4.65/1.83  
% 4.65/1.83  %Background operators:
% 4.65/1.83  
% 4.65/1.83  
% 4.65/1.83  %Foreground operators:
% 4.65/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.65/1.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.65/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.65/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.65/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.65/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.65/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.65/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.65/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.65/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.65/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.65/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.83  
% 4.65/1.84  tff(f_101, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 4.65/1.84  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 4.65/1.84  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.65/1.84  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.65/1.84  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.65/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.65/1.84  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.65/1.84  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.65/1.84  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.65/1.84  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 4.65/1.84  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_48, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_44, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_40, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_318, plain, (![D_77, C_78, B_79, A_80]: (k1_funct_1(k2_funct_1(D_77), k1_funct_1(D_77, C_78))=C_78 | k1_xboole_0=B_79 | ~r2_hidden(C_78, A_80) | ~v2_funct_1(D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_2(D_77, A_80, B_79) | ~v1_funct_1(D_77))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.65/1.84  tff(c_365, plain, (![D_82, B_83]: (k1_funct_1(k2_funct_1(D_82), k1_funct_1(D_82, '#skF_4'))='#skF_4' | k1_xboole_0=B_83 | ~v2_funct_1(D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_83))) | ~v1_funct_2(D_82, '#skF_1', B_83) | ~v1_funct_1(D_82))), inference(resolution, [status(thm)], [c_40, c_318])).
% 4.65/1.84  tff(c_370, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_365])).
% 4.65/1.84  tff(c_377, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_370])).
% 4.65/1.84  tff(c_399, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_377])).
% 4.65/1.84  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.65/1.84  tff(c_416, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_399, c_8])).
% 4.65/1.84  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.84  tff(c_413, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_399, c_399, c_12])).
% 4.65/1.84  tff(c_87, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.84  tff(c_95, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_87])).
% 4.65/1.84  tff(c_96, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.84  tff(c_103, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_95, c_96])).
% 4.65/1.84  tff(c_122, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_103])).
% 4.65/1.84  tff(c_492, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_122])).
% 4.65/1.84  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_416, c_492])).
% 4.65/1.84  tff(c_499, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_377])).
% 4.65/1.84  tff(c_498, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_377])).
% 4.65/1.84  tff(c_38, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.65/1.84  tff(c_587, plain, (![D_104, B_105]: (k1_funct_1(k2_funct_1(D_104), k1_funct_1(D_104, '#skF_3'))='#skF_3' | k1_xboole_0=B_105 | ~v2_funct_1(D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_105))) | ~v1_funct_2(D_104, '#skF_1', B_105) | ~v1_funct_1(D_104))), inference(resolution, [status(thm)], [c_42, c_318])).
% 4.65/1.84  tff(c_592, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_587])).
% 4.65/1.84  tff(c_599, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_498, c_38, c_592])).
% 4.65/1.84  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_36, c_599])).
% 4.65/1.84  tff(c_602, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_103])).
% 4.65/1.84  tff(c_605, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_46])).
% 4.65/1.84  tff(c_874, plain, (![D_150, C_151, B_152, A_153]: (k1_funct_1(k2_funct_1(D_150), k1_funct_1(D_150, C_151))=C_151 | k1_xboole_0=B_152 | ~r2_hidden(C_151, A_153) | ~v2_funct_1(D_150) | ~m1_subset_1(D_150, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))) | ~v1_funct_2(D_150, A_153, B_152) | ~v1_funct_1(D_150))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.65/1.84  tff(c_940, plain, (![D_161, B_162]: (k1_funct_1(k2_funct_1(D_161), k1_funct_1(D_161, '#skF_4'))='#skF_4' | k1_xboole_0=B_162 | ~v2_funct_1(D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_162))) | ~v1_funct_2(D_161, '#skF_1', B_162) | ~v1_funct_1(D_161))), inference(resolution, [status(thm)], [c_40, c_874])).
% 4.65/1.84  tff(c_942, plain, (![D_161]: (k1_funct_1(k2_funct_1(D_161), k1_funct_1(D_161, '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1(D_161) | ~m1_subset_1(D_161, k1_zfmisc_1('#skF_2')) | ~v1_funct_2(D_161, '#skF_1', '#skF_1') | ~v1_funct_1(D_161))), inference(superposition, [status(thm), theory('equality')], [c_602, c_940])).
% 4.65/1.84  tff(c_1151, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_942])).
% 4.65/1.84  tff(c_619, plain, (![B_106, A_107]: (k1_xboole_0=B_106 | k1_xboole_0=A_107 | k2_zfmisc_1(A_107, B_106)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.84  tff(c_622, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_602, c_619])).
% 4.65/1.84  tff(c_640, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_622])).
% 4.65/1.84  tff(c_1170, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_640])).
% 4.65/1.84  tff(c_1173, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_1151, c_12])).
% 4.65/1.84  tff(c_1253, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1173, c_602])).
% 4.65/1.84  tff(c_1255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1170, c_1253])).
% 4.65/1.84  tff(c_2211, plain, (![D_242]: (k1_funct_1(k2_funct_1(D_242), k1_funct_1(D_242, '#skF_4'))='#skF_4' | ~v2_funct_1(D_242) | ~m1_subset_1(D_242, k1_zfmisc_1('#skF_2')) | ~v1_funct_2(D_242, '#skF_1', '#skF_1') | ~v1_funct_1(D_242))), inference(splitRight, [status(thm)], [c_942])).
% 4.65/1.84  tff(c_1257, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_942])).
% 4.65/1.84  tff(c_1061, plain, (![D_179, B_180]: (k1_funct_1(k2_funct_1(D_179), k1_funct_1(D_179, '#skF_3'))='#skF_3' | k1_xboole_0=B_180 | ~v2_funct_1(D_179) | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_180))) | ~v1_funct_2(D_179, '#skF_1', B_180) | ~v1_funct_1(D_179))), inference(resolution, [status(thm)], [c_42, c_874])).
% 4.65/1.84  tff(c_1063, plain, (![D_179]: (k1_funct_1(k2_funct_1(D_179), k1_funct_1(D_179, '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1(D_179) | ~m1_subset_1(D_179, k1_zfmisc_1('#skF_2')) | ~v1_funct_2(D_179, '#skF_1', '#skF_1') | ~v1_funct_1(D_179))), inference(superposition, [status(thm), theory('equality')], [c_602, c_1061])).
% 4.65/1.84  tff(c_1284, plain, (![D_198]: (k1_funct_1(k2_funct_1(D_198), k1_funct_1(D_198, '#skF_3'))='#skF_3' | ~v2_funct_1(D_198) | ~m1_subset_1(D_198, k1_zfmisc_1('#skF_2')) | ~v1_funct_2(D_198, '#skF_1', '#skF_1') | ~v1_funct_1(D_198))), inference(negUnitSimplification, [status(thm)], [c_1257, c_1063])).
% 4.65/1.84  tff(c_1310, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_38, c_1284])).
% 4.65/1.84  tff(c_1316, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_605, c_44, c_1310])).
% 4.65/1.84  tff(c_2220, plain, ('#skF_3'='#skF_4' | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2211, c_1316])).
% 4.65/1.84  tff(c_2246, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_605, c_44, c_2220])).
% 4.65/1.84  tff(c_2248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_2246])).
% 4.65/1.84  tff(c_2250, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_622])).
% 4.65/1.84  tff(c_2249, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_622])).
% 4.65/1.84  tff(c_2294, plain, ('#skF_2'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2250, c_2249])).
% 4.65/1.84  tff(c_2295, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_2294])).
% 4.65/1.84  tff(c_24, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.65/1.84  tff(c_609, plain, (v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_602, c_24])).
% 4.65/1.84  tff(c_2316, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_609])).
% 4.65/1.84  tff(c_2321, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_50])).
% 4.65/1.84  tff(c_2320, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_44])).
% 4.65/1.85  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.85  tff(c_2255, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2250, c_14])).
% 4.65/1.85  tff(c_2311, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_2295, c_2255])).
% 4.65/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.85  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.85  tff(c_2349, plain, (![C_250, A_251, B_252]: (v4_relat_1(C_250, A_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.65/1.85  tff(c_2530, plain, (![A_279, A_280, B_281]: (v4_relat_1(A_279, A_280) | ~r1_tarski(A_279, k2_zfmisc_1(A_280, B_281)))), inference(resolution, [status(thm)], [c_18, c_2349])).
% 4.65/1.85  tff(c_2552, plain, (![A_280, B_281]: (v4_relat_1(k2_zfmisc_1(A_280, B_281), A_280))), inference(resolution, [status(thm)], [c_6, c_2530])).
% 4.65/1.85  tff(c_2430, plain, (![B_258, A_259]: (r1_tarski(k1_relat_1(B_258), A_259) | ~v4_relat_1(B_258, A_259) | ~v1_relat_1(B_258))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.65/1.85  tff(c_104, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_96])).
% 4.65/1.85  tff(c_2252, plain, (![A_3]: (A_3='#skF_2' | ~r1_tarski(A_3, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2250, c_2250, c_104])).
% 4.65/1.85  tff(c_2399, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_2295, c_2252])).
% 4.65/1.85  tff(c_2584, plain, (![B_290]: (k1_relat_1(B_290)='#skF_1' | ~v4_relat_1(B_290, '#skF_1') | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_2430, c_2399])).
% 4.65/1.85  tff(c_2588, plain, (![B_281]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_281))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_281)))), inference(resolution, [status(thm)], [c_2552, c_2584])).
% 4.65/1.85  tff(c_2599, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2311, c_2588])).
% 4.65/1.85  tff(c_2318, plain, (k1_funct_1('#skF_1', '#skF_3')=k1_funct_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2295, c_2295, c_38])).
% 4.65/1.85  tff(c_2475, plain, (![B_272, A_273]: (k1_funct_1(k2_funct_1(B_272), k1_funct_1(B_272, A_273))=A_273 | ~r2_hidden(A_273, k1_relat_1(B_272)) | ~v2_funct_1(B_272) | ~v1_funct_1(B_272) | ~v1_relat_1(B_272))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.85  tff(c_2493, plain, (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2318, c_2475])).
% 4.65/1.85  tff(c_2497, plain, (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_4'))='#skF_3' | ~r2_hidden('#skF_3', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2316, c_2321, c_2320, c_2493])).
% 4.65/1.85  tff(c_2824, plain, (k1_funct_1(k2_funct_1('#skF_1'), k1_funct_1('#skF_1', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2599, c_2497])).
% 4.65/1.85  tff(c_28, plain, (![B_13, A_12]: (k1_funct_1(k2_funct_1(B_13), k1_funct_1(B_13, A_12))=A_12 | ~r2_hidden(A_12, k1_relat_1(B_13)) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.65/1.85  tff(c_2831, plain, ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2824, c_28])).
% 4.65/1.85  tff(c_2838, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2316, c_2321, c_2320, c_40, c_2599, c_2831])).
% 4.65/1.85  tff(c_2840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_2838])).
% 4.65/1.85  tff(c_2841, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2294])).
% 4.65/1.85  tff(c_2842, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_2294])).
% 4.65/1.85  tff(c_2865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2841, c_2842])).
% 4.65/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.65/1.85  
% 4.65/1.85  Inference rules
% 4.65/1.85  ----------------------
% 4.65/1.85  #Ref     : 0
% 4.65/1.85  #Sup     : 591
% 4.65/1.85  #Fact    : 0
% 4.65/1.85  #Define  : 0
% 4.65/1.85  #Split   : 7
% 4.65/1.85  #Chain   : 0
% 4.65/1.85  #Close   : 0
% 4.65/1.85  
% 4.65/1.85  Ordering : KBO
% 4.65/1.85  
% 4.65/1.85  Simplification rules
% 4.65/1.85  ----------------------
% 4.65/1.85  #Subsume      : 89
% 4.65/1.85  #Demod        : 676
% 4.65/1.85  #Tautology    : 255
% 4.65/1.85  #SimpNegUnit  : 9
% 4.65/1.85  #BackRed      : 76
% 4.65/1.85  
% 4.65/1.85  #Partial instantiations: 0
% 4.65/1.85  #Strategies tried      : 1
% 4.65/1.85  
% 4.65/1.85  Timing (in seconds)
% 4.65/1.85  ----------------------
% 4.65/1.85  Preprocessing        : 0.32
% 4.65/1.85  Parsing              : 0.17
% 4.65/1.85  CNF conversion       : 0.02
% 4.65/1.85  Main loop            : 0.75
% 4.65/1.85  Inferencing          : 0.26
% 4.65/1.85  Reduction            : 0.26
% 4.65/1.85  Demodulation         : 0.19
% 4.65/1.85  BG Simplification    : 0.03
% 4.65/1.85  Subsumption          : 0.15
% 4.65/1.85  Abstraction          : 0.03
% 4.65/1.85  MUC search           : 0.00
% 4.65/1.85  Cooper               : 0.00
% 4.65/1.85  Total                : 1.11
% 4.65/1.85  Index Insertion      : 0.00
% 4.65/1.85  Index Deletion       : 0.00
% 4.65/1.85  Index Matching       : 0.00
% 4.65/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
