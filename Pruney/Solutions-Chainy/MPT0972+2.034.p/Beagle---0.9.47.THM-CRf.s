%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:39 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 353 expanded)
%              Number of leaves         :   33 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 (1093 expanded)
%              Number of equality atoms :   60 ( 280 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_707,plain,(
    ! [A_142,B_143,D_144] :
      ( r2_relset_1(A_142,B_143,D_144,D_144)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_719,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_707])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_117,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_133,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_117])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_844,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_867,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_844])).

tff(c_989,plain,(
    ! [B_181,A_182,C_183] :
      ( k1_xboole_0 = B_181
      | k1_relset_1(A_182,B_181,C_183) = A_182
      | ~ v1_funct_2(C_183,A_182,B_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_182,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_999,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_989])).

tff(c_1016,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_867,c_999])).

tff(c_1026,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1016])).

tff(c_132,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_117])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_866,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_844])).

tff(c_996,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_989])).

tff(c_1013,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_866,c_996])).

tff(c_1020,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1013])).

tff(c_1074,plain,(
    ! [A_193,B_194] :
      ( r2_hidden('#skF_2'(A_193,B_194),k1_relat_1(A_193))
      | B_194 = A_193
      | k1_relat_1(B_194) != k1_relat_1(A_193)
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194)
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1085,plain,(
    ! [B_194] :
      ( r2_hidden('#skF_2'('#skF_6',B_194),'#skF_3')
      | B_194 = '#skF_6'
      | k1_relat_1(B_194) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_1074])).

tff(c_1192,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_2'('#skF_6',B_209),'#skF_3')
      | B_209 = '#skF_6'
      | k1_relat_1(B_209) != '#skF_3'
      | ~ v1_funct_1(B_209)
      | ~ v1_relat_1(B_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_54,c_1020,c_1085])).

tff(c_48,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1257,plain,(
    ! [B_223] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_223)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_223))
      | B_223 = '#skF_6'
      | k1_relat_1(B_223) != '#skF_3'
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223) ) ),
    inference(resolution,[status(thm)],[c_1192,c_48])).

tff(c_22,plain,(
    ! [B_21,A_17] :
      ( k1_funct_1(B_21,'#skF_2'(A_17,B_21)) != k1_funct_1(A_17,'#skF_2'(A_17,B_21))
      | B_21 = A_17
      | k1_relat_1(B_21) != k1_relat_1(A_17)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1264,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_22])).

tff(c_1271,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_60,c_1026,c_132,c_54,c_1020,c_1026,c_1264])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1288,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_46])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1288])).

tff(c_1299,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1016])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1326,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1324,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1299,c_12])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [C_61,A_62,B_63] :
      ( r2_hidden(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_739,plain,(
    ! [A_151,A_152] :
      ( r2_hidden('#skF_1'(A_151),A_152)
      | ~ m1_subset_1(A_151,k1_zfmisc_1(A_152))
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_4,c_158])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_756,plain,(
    ! [A_153,A_154] :
      ( ~ v1_xboole_0(A_153)
      | ~ m1_subset_1(A_154,k1_zfmisc_1(A_153))
      | v1_xboole_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_739,c_2])).

tff(c_766,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_756])).

tff(c_777,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_766])).

tff(c_1395,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_777])).

tff(c_1402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1395])).

tff(c_1403,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1013])).

tff(c_1430,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_6])).

tff(c_1428,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1403,c_12])).

tff(c_1496,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_777])).

tff(c_1503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_1496])).

tff(c_1504,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_1505,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_766])).

tff(c_96,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | B_48 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_1511,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1504,c_99])).

tff(c_1536,plain,(
    ! [A_236] :
      ( A_236 = '#skF_6'
      | ~ v1_xboole_0(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_99])).

tff(c_1543,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1505,c_1536])).

tff(c_1623,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_56])).

tff(c_755,plain,(
    ! [A_152,A_151] :
      ( ~ v1_xboole_0(A_152)
      | ~ m1_subset_1(A_151,k1_zfmisc_1(A_152))
      | v1_xboole_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_739,c_2])).

tff(c_1638,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1623,c_755])).

tff(c_1643,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1504,c_1638])).

tff(c_1521,plain,(
    ! [A_49] :
      ( A_49 = '#skF_6'
      | ~ v1_xboole_0(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_99])).

tff(c_1650,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1643,c_1521])).

tff(c_1659,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_46])).

tff(c_1668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_1659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.65  
% 3.81/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.65  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.81/1.65  
% 3.81/1.65  %Foreground sorts:
% 3.81/1.65  
% 3.81/1.65  
% 3.81/1.65  %Background operators:
% 3.81/1.65  
% 3.81/1.65  
% 3.81/1.65  %Foreground operators:
% 3.81/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.65  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.81/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.81/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.81/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.81/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.81/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.81/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.81/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.81/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.81/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.81/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.65  
% 3.81/1.67  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 3.81/1.67  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.81/1.67  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.81/1.67  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.81/1.67  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.81/1.67  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 3.81/1.67  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.81/1.67  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.81/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.81/1.67  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.81/1.67  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.81/1.67  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_707, plain, (![A_142, B_143, D_144]: (r2_relset_1(A_142, B_143, D_144, D_144) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.81/1.67  tff(c_719, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_707])).
% 3.81/1.67  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_117, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.81/1.67  tff(c_133, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_117])).
% 3.81/1.67  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_844, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.81/1.67  tff(c_867, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_844])).
% 3.81/1.67  tff(c_989, plain, (![B_181, A_182, C_183]: (k1_xboole_0=B_181 | k1_relset_1(A_182, B_181, C_183)=A_182 | ~v1_funct_2(C_183, A_182, B_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_182, B_181))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.81/1.67  tff(c_999, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_989])).
% 3.81/1.67  tff(c_1016, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_867, c_999])).
% 3.81/1.67  tff(c_1026, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1016])).
% 3.81/1.67  tff(c_132, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_117])).
% 3.81/1.67  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_866, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_844])).
% 3.81/1.67  tff(c_996, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_989])).
% 3.81/1.67  tff(c_1013, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_866, c_996])).
% 3.81/1.67  tff(c_1020, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_1013])).
% 3.81/1.67  tff(c_1074, plain, (![A_193, B_194]: (r2_hidden('#skF_2'(A_193, B_194), k1_relat_1(A_193)) | B_194=A_193 | k1_relat_1(B_194)!=k1_relat_1(A_193) | ~v1_funct_1(B_194) | ~v1_relat_1(B_194) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.67  tff(c_1085, plain, (![B_194]: (r2_hidden('#skF_2'('#skF_6', B_194), '#skF_3') | B_194='#skF_6' | k1_relat_1(B_194)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_194) | ~v1_relat_1(B_194) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1020, c_1074])).
% 3.81/1.67  tff(c_1192, plain, (![B_209]: (r2_hidden('#skF_2'('#skF_6', B_209), '#skF_3') | B_209='#skF_6' | k1_relat_1(B_209)!='#skF_3' | ~v1_funct_1(B_209) | ~v1_relat_1(B_209))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_54, c_1020, c_1085])).
% 3.81/1.67  tff(c_48, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_1257, plain, (![B_223]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_223))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_223)) | B_223='#skF_6' | k1_relat_1(B_223)!='#skF_3' | ~v1_funct_1(B_223) | ~v1_relat_1(B_223))), inference(resolution, [status(thm)], [c_1192, c_48])).
% 3.81/1.67  tff(c_22, plain, (![B_21, A_17]: (k1_funct_1(B_21, '#skF_2'(A_17, B_21))!=k1_funct_1(A_17, '#skF_2'(A_17, B_21)) | B_21=A_17 | k1_relat_1(B_21)!=k1_relat_1(A_17) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.67  tff(c_1264, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1257, c_22])).
% 3.81/1.67  tff(c_1271, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_60, c_1026, c_132, c_54, c_1020, c_1026, c_1264])).
% 3.81/1.67  tff(c_46, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.81/1.67  tff(c_1288, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_46])).
% 3.81/1.67  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_719, c_1288])).
% 3.81/1.67  tff(c_1299, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1016])).
% 3.81/1.67  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.81/1.67  tff(c_1326, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_6])).
% 3.81/1.67  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.81/1.67  tff(c_1324, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1299, c_12])).
% 3.81/1.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.67  tff(c_158, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.81/1.67  tff(c_739, plain, (![A_151, A_152]: (r2_hidden('#skF_1'(A_151), A_152) | ~m1_subset_1(A_151, k1_zfmisc_1(A_152)) | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_4, c_158])).
% 3.81/1.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.81/1.67  tff(c_756, plain, (![A_153, A_154]: (~v1_xboole_0(A_153) | ~m1_subset_1(A_154, k1_zfmisc_1(A_153)) | v1_xboole_0(A_154))), inference(resolution, [status(thm)], [c_739, c_2])).
% 3.81/1.67  tff(c_766, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_756])).
% 3.81/1.67  tff(c_777, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_766])).
% 3.81/1.67  tff(c_1395, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_777])).
% 3.81/1.67  tff(c_1402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1395])).
% 3.81/1.67  tff(c_1403, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1013])).
% 3.81/1.67  tff(c_1430, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_6])).
% 3.81/1.67  tff(c_1428, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1403, c_12])).
% 3.81/1.67  tff(c_1496, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_777])).
% 3.81/1.67  tff(c_1503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1430, c_1496])).
% 3.81/1.67  tff(c_1504, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_766])).
% 3.81/1.67  tff(c_1505, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_766])).
% 3.81/1.67  tff(c_96, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | B_48=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.81/1.67  tff(c_99, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_6, c_96])).
% 3.81/1.67  tff(c_1511, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1504, c_99])).
% 3.81/1.67  tff(c_1536, plain, (![A_236]: (A_236='#skF_6' | ~v1_xboole_0(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_1511, c_99])).
% 3.81/1.67  tff(c_1543, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_1505, c_1536])).
% 3.81/1.67  tff(c_1623, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_56])).
% 3.81/1.67  tff(c_755, plain, (![A_152, A_151]: (~v1_xboole_0(A_152) | ~m1_subset_1(A_151, k1_zfmisc_1(A_152)) | v1_xboole_0(A_151))), inference(resolution, [status(thm)], [c_739, c_2])).
% 3.81/1.67  tff(c_1638, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1623, c_755])).
% 3.81/1.67  tff(c_1643, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1504, c_1638])).
% 3.81/1.67  tff(c_1521, plain, (![A_49]: (A_49='#skF_6' | ~v1_xboole_0(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_1511, c_99])).
% 3.81/1.67  tff(c_1650, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1643, c_1521])).
% 3.81/1.67  tff(c_1659, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_46])).
% 3.81/1.67  tff(c_1668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_719, c_1659])).
% 3.81/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.67  
% 3.81/1.67  Inference rules
% 3.81/1.67  ----------------------
% 3.81/1.67  #Ref     : 1
% 3.81/1.67  #Sup     : 315
% 3.81/1.67  #Fact    : 0
% 3.81/1.67  #Define  : 0
% 3.81/1.67  #Split   : 13
% 3.81/1.67  #Chain   : 0
% 3.81/1.67  #Close   : 0
% 3.81/1.67  
% 3.81/1.67  Ordering : KBO
% 3.81/1.67  
% 3.81/1.67  Simplification rules
% 3.81/1.67  ----------------------
% 3.81/1.67  #Subsume      : 63
% 3.81/1.67  #Demod        : 384
% 3.81/1.67  #Tautology    : 176
% 3.81/1.67  #SimpNegUnit  : 24
% 3.81/1.67  #BackRed      : 158
% 3.81/1.67  
% 3.81/1.67  #Partial instantiations: 0
% 3.81/1.67  #Strategies tried      : 1
% 3.81/1.67  
% 3.81/1.67  Timing (in seconds)
% 3.81/1.67  ----------------------
% 3.81/1.67  Preprocessing        : 0.34
% 3.81/1.67  Parsing              : 0.18
% 3.81/1.67  CNF conversion       : 0.02
% 3.81/1.67  Main loop            : 0.55
% 3.81/1.67  Inferencing          : 0.19
% 3.81/1.67  Reduction            : 0.18
% 3.81/1.67  Demodulation         : 0.12
% 3.81/1.67  BG Simplification    : 0.03
% 3.81/1.67  Subsumption          : 0.10
% 3.81/1.67  Abstraction          : 0.03
% 3.81/1.67  MUC search           : 0.00
% 3.81/1.67  Cooper               : 0.00
% 3.81/1.67  Total                : 0.93
% 3.81/1.67  Index Insertion      : 0.00
% 3.81/1.67  Index Deletion       : 0.00
% 3.81/1.67  Index Matching       : 0.00
% 3.81/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
