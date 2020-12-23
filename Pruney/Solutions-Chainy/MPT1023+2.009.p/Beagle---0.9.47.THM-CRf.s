%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :  223 (1439 expanded)
%              Number of leaves         :   34 ( 470 expanded)
%              Depth                    :   20
%              Number of atoms          :  477 (4236 expanded)
%              Number of equality atoms :  167 ( 996 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_68,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_142,plain,(
    ! [C_62,B_63,A_64] :
      ( v1_xboole_0(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(B_63,A_64)))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_154,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_142])).

tff(c_156,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_403,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_432,plain,(
    ! [C_111] :
      ( r2_relset_1('#skF_2','#skF_3',C_111,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_403])).

tff(c_442,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_432])).

tff(c_96,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_96])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_172,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_184,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_172])).

tff(c_443,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_456,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_443])).

tff(c_464,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_184,c_456])).

tff(c_468,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_109,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_96])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_185,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_172])).

tff(c_459,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_443])).

tff(c_467,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_185,c_459])).

tff(c_474,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_566,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_1'(A_124,B_125),k1_relat_1(A_124))
      | B_125 = A_124
      | k1_relat_1(B_125) != k1_relat_1(A_124)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_571,plain,(
    ! [B_125] :
      ( r2_hidden('#skF_1'('#skF_4',B_125),'#skF_2')
      | B_125 = '#skF_4'
      | k1_relat_1(B_125) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_566])).

tff(c_661,plain,(
    ! [B_140] :
      ( r2_hidden('#skF_1'('#skF_4',B_140),'#skF_2')
      | B_140 = '#skF_4'
      | k1_relat_1(B_140) != '#skF_2'
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_56,c_474,c_571])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_130,plain,(
    ! [A_57,C_58,B_59] :
      ( m1_subset_1(A_57,C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_137,plain,(
    ! [A_57,B_6,A_5] :
      ( m1_subset_1(A_57,B_6)
      | ~ r2_hidden(A_57,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_130])).

tff(c_1623,plain,(
    ! [B_206,B_207] :
      ( m1_subset_1('#skF_1'('#skF_4',B_206),B_207)
      | ~ r1_tarski('#skF_2',B_207)
      | B_206 = '#skF_4'
      | k1_relat_1(B_206) != '#skF_2'
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(resolution,[status(thm)],[c_661,c_137])).

tff(c_44,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_4',E_37)
      | ~ m1_subset_1(E_37,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1685,plain,(
    ! [B_206] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_206)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_206))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_206 = '#skF_4'
      | k1_relat_1(B_206) != '#skF_2'
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(resolution,[status(thm)],[c_1623,c_44])).

tff(c_2009,plain,(
    ! [B_233] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_233)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_233))
      | B_233 = '#skF_4'
      | k1_relat_1(B_233) != '#skF_2'
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1685])).

tff(c_18,plain,(
    ! [B_14,A_10] :
      ( k1_funct_1(B_14,'#skF_1'(A_10,B_14)) != k1_funct_1(A_10,'#skF_1'(A_10,B_14))
      | B_14 = A_10
      | k1_relat_1(B_14) != k1_relat_1(A_10)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2016,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2009,c_18])).

tff(c_2023,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50,c_468,c_109,c_56,c_468,c_474,c_2016])).

tff(c_42,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2036,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_42])).

tff(c_2047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_2036])).

tff(c_2048,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2069,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_2])).

tff(c_2071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2069])).

tff(c_2072,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_2093,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2072,c_2])).

tff(c_2095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_2093])).

tff(c_2097,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_155,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_142])).

tff(c_2154,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2097,c_155])).

tff(c_2277,plain,(
    ! [A_245,A_246,B_247] :
      ( v1_xboole_0(A_245)
      | ~ v1_xboole_0(A_246)
      | ~ r1_tarski(A_245,k2_zfmisc_1(B_247,A_246)) ) ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_2290,plain,(
    ! [B_248,A_249] :
      ( v1_xboole_0(k2_zfmisc_1(B_248,A_249))
      | ~ v1_xboole_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_8,c_2277])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | B_4 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2158,plain,(
    ! [A_237] :
      ( A_237 = '#skF_3'
      | ~ v1_xboole_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_2097,c_10])).

tff(c_2165,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2154,c_2158])).

tff(c_59,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | B_39 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_2,c_59])).

tff(c_2110,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2097,c_62])).

tff(c_2096,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_2103,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2096,c_62])).

tff(c_2133,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2110,c_2103])).

tff(c_2172,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2165,c_2133])).

tff(c_2104,plain,(
    ! [A_3] :
      ( A_3 = '#skF_5'
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_2096,c_10])).

tff(c_2201,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ v1_xboole_0(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2172,c_2104])).

tff(c_2298,plain,(
    ! [B_250,A_251] :
      ( k2_zfmisc_1(B_250,A_251) = '#skF_4'
      | ~ v1_xboole_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_2290,c_2201])).

tff(c_2304,plain,(
    ! [B_250] : k2_zfmisc_1(B_250,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2154,c_2298])).

tff(c_70,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_81,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_70])).

tff(c_83,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_81,c_83])).

tff(c_129,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_2140,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2133,c_129])).

tff(c_2227,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2165,c_2165,c_2140])).

tff(c_2307,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2304,c_2227])).

tff(c_2312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2307])).

tff(c_2313,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_2319,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_52])).

tff(c_2464,plain,(
    ! [A_272,B_273,C_274] :
      ( k1_relset_1(A_272,B_273,C_274) = k1_relat_1(C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2495,plain,(
    ! [C_278] :
      ( k1_relset_1('#skF_2','#skF_3',C_278) = k1_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2313,c_2464])).

tff(c_2507,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2319,c_2495])).

tff(c_2335,plain,(
    ! [C_252,B_253,A_254] :
      ( v1_xboole_0(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(B_253,A_254)))
      | ~ v1_xboole_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2338,plain,(
    ! [C_252] :
      ( v1_xboole_0(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1('#skF_5'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2313,c_2335])).

tff(c_2383,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2338])).

tff(c_2692,plain,(
    ! [B_309,C_310,A_311] :
      ( k1_xboole_0 = B_309
      | v1_funct_2(C_310,A_311,B_309)
      | k1_relset_1(A_311,B_309,C_310) != A_311
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_311,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2701,plain,(
    ! [C_310] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_310,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_310) != '#skF_2'
      | ~ m1_subset_1(C_310,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2313,c_2692])).

tff(c_2807,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2701])).

tff(c_2831,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2807,c_2])).

tff(c_2833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2383,c_2831])).

tff(c_2835,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2701])).

tff(c_2852,plain,(
    ! [B_330,A_331,C_332] :
      ( k1_xboole_0 = B_330
      | k1_relset_1(A_331,B_330,C_332) = A_331
      | ~ v1_funct_2(C_332,A_331,B_330)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2861,plain,(
    ! [C_332] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_332) = '#skF_2'
      | ~ v1_funct_2(C_332,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_332,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2313,c_2852])).

tff(c_2887,plain,(
    ! [C_336] :
      ( k1_relset_1('#skF_2','#skF_3',C_336) = '#skF_2'
      | ~ v1_funct_2(C_336,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_336,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2835,c_2861])).

tff(c_2893,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2319,c_2887])).

tff(c_2903,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2507,c_2893])).

tff(c_2318,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_46])).

tff(c_2506,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2318,c_2495])).

tff(c_2890,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2318,c_2887])).

tff(c_2900,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2506,c_2890])).

tff(c_2919,plain,(
    ! [A_337,B_338] :
      ( r2_hidden('#skF_1'(A_337,B_338),k1_relat_1(A_337))
      | B_338 = A_337
      | k1_relat_1(B_338) != k1_relat_1(A_337)
      | ~ v1_funct_1(B_338)
      | ~ v1_relat_1(B_338)
      | ~ v1_funct_1(A_337)
      | ~ v1_relat_1(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2927,plain,(
    ! [B_338] :
      ( r2_hidden('#skF_1'('#skF_5',B_338),'#skF_2')
      | B_338 = '#skF_5'
      | k1_relat_1(B_338) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_338)
      | ~ v1_relat_1(B_338)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_2919])).

tff(c_2966,plain,(
    ! [B_341] :
      ( r2_hidden('#skF_1'('#skF_5',B_341),'#skF_2')
      | B_341 = '#skF_5'
      | k1_relat_1(B_341) != '#skF_2'
      | ~ v1_funct_1(B_341)
      | ~ v1_relat_1(B_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50,c_2900,c_2927])).

tff(c_2384,plain,(
    ! [A_257,C_258,B_259] :
      ( m1_subset_1(A_257,C_258)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(C_258))
      | ~ r2_hidden(A_257,B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2393,plain,(
    ! [A_257,B_6,A_5] :
      ( m1_subset_1(A_257,B_6)
      | ~ r2_hidden(A_257,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_2384])).

tff(c_3461,plain,(
    ! [B_378,B_379] :
      ( m1_subset_1('#skF_1'('#skF_5',B_378),B_379)
      | ~ r1_tarski('#skF_2',B_379)
      | B_378 = '#skF_5'
      | k1_relat_1(B_378) != '#skF_2'
      | ~ v1_funct_1(B_378)
      | ~ v1_relat_1(B_378) ) ),
    inference(resolution,[status(thm)],[c_2966,c_2393])).

tff(c_3539,plain,(
    ! [B_378] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_5',B_378)) = k1_funct_1('#skF_4','#skF_1'('#skF_5',B_378))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_378 = '#skF_5'
      | k1_relat_1(B_378) != '#skF_2'
      | ~ v1_funct_1(B_378)
      | ~ v1_relat_1(B_378) ) ),
    inference(resolution,[status(thm)],[c_3461,c_44])).

tff(c_3883,plain,(
    ! [B_407] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_5',B_407)) = k1_funct_1('#skF_4','#skF_1'('#skF_5',B_407))
      | B_407 = '#skF_5'
      | k1_relat_1(B_407) != '#skF_2'
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3539])).

tff(c_3889,plain,(
    ! [B_407] :
      ( k1_funct_1(B_407,'#skF_1'('#skF_5',B_407)) != k1_funct_1('#skF_4','#skF_1'('#skF_5',B_407))
      | B_407 = '#skF_5'
      | k1_relat_1(B_407) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | B_407 = '#skF_5'
      | k1_relat_1(B_407) != '#skF_2'
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3883,c_18])).

tff(c_3895,plain,(
    ! [B_407] :
      ( k1_funct_1(B_407,'#skF_1'('#skF_5',B_407)) != k1_funct_1('#skF_4','#skF_1'('#skF_5',B_407))
      | B_407 = '#skF_5'
      | k1_relat_1(B_407) != '#skF_2'
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50,c_2900,c_3889])).

tff(c_4225,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3895])).

tff(c_4227,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_56,c_2903,c_4225])).

tff(c_82,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_70])).

tff(c_90,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_83])).

tff(c_128,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_2315,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_128])).

tff(c_4258,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4227,c_2315])).

tff(c_4271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4258])).

tff(c_4306,plain,(
    ! [C_443] :
      ( v1_xboole_0(C_443)
      | ~ m1_subset_1(C_443,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_2338])).

tff(c_4318,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2319,c_4306])).

tff(c_4273,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2338])).

tff(c_4280,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_4273,c_10])).

tff(c_4332,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4318,c_4280])).

tff(c_4317,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2318,c_4306])).

tff(c_4325,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4317,c_4280])).

tff(c_4342,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4325,c_2315])).

tff(c_4382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4332,c_4342])).

tff(c_4383,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_4389,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_52])).

tff(c_4493,plain,(
    ! [A_464,B_465,C_466] :
      ( k1_relset_1(A_464,B_465,C_466) = k1_relat_1(C_466)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4576,plain,(
    ! [C_479] :
      ( k1_relset_1('#skF_2','#skF_3',C_479) = k1_relat_1(C_479)
      | ~ m1_subset_1(C_479,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_4493])).

tff(c_4587,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4389,c_4576])).

tff(c_4458,plain,(
    ! [C_455,B_456,A_457] :
      ( v1_xboole_0(C_455)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(B_456,A_457)))
      | ~ v1_xboole_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4461,plain,(
    ! [C_455] :
      ( v1_xboole_0(C_455)
      | ~ m1_subset_1(C_455,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_4458])).

tff(c_4467,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4461])).

tff(c_4923,plain,(
    ! [B_527,C_528,A_529] :
      ( k1_xboole_0 = B_527
      | v1_funct_2(C_528,A_529,B_527)
      | k1_relset_1(A_529,B_527,C_528) != A_529
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_529,B_527))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4932,plain,(
    ! [C_528] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_528,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_528) != '#skF_2'
      | ~ m1_subset_1(C_528,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_4923])).

tff(c_4957,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4932])).

tff(c_4985,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4957,c_2])).

tff(c_4987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4467,c_4985])).

tff(c_4989,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4932])).

tff(c_4799,plain,(
    ! [B_506,A_507,C_508] :
      ( k1_xboole_0 = B_506
      | k1_relset_1(A_507,B_506,C_508) = A_507
      | ~ v1_funct_2(C_508,A_507,B_506)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_507,B_506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4808,plain,(
    ! [C_508] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_508) = '#skF_2'
      | ~ v1_funct_2(C_508,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_508,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_4799])).

tff(c_5037,plain,(
    ! [C_542] :
      ( k1_relset_1('#skF_2','#skF_3',C_542) = '#skF_2'
      | ~ v1_funct_2(C_542,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_542,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4989,c_4808])).

tff(c_5040,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_4389,c_5037])).

tff(c_5050,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4587,c_5040])).

tff(c_4388,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_46])).

tff(c_4588,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4388,c_4576])).

tff(c_5043,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_4388,c_5037])).

tff(c_5053,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4588,c_5043])).

tff(c_20,plain,(
    ! [A_10,B_14] :
      ( r2_hidden('#skF_1'(A_10,B_14),k1_relat_1(A_10))
      | B_14 = A_10
      | k1_relat_1(B_14) != k1_relat_1(A_10)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5069,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_1'('#skF_5',B_14),'#skF_2')
      | B_14 = '#skF_5'
      | k1_relat_1(B_14) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5053,c_20])).

tff(c_5169,plain,(
    ! [B_550] :
      ( r2_hidden('#skF_1'('#skF_5',B_550),'#skF_2')
      | B_550 = '#skF_5'
      | k1_relat_1(B_550) != '#skF_2'
      | ~ v1_funct_1(B_550)
      | ~ v1_relat_1(B_550) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50,c_5053,c_5069])).

tff(c_4416,plain,(
    ! [A_445,C_446,B_447] :
      ( m1_subset_1(A_445,C_446)
      | ~ m1_subset_1(B_447,k1_zfmisc_1(C_446))
      | ~ r2_hidden(A_445,B_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4425,plain,(
    ! [A_445,B_6,A_5] :
      ( m1_subset_1(A_445,B_6)
      | ~ r2_hidden(A_445,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_4416])).

tff(c_5569,plain,(
    ! [B_577,B_578] :
      ( m1_subset_1('#skF_1'('#skF_5',B_577),B_578)
      | ~ r1_tarski('#skF_2',B_578)
      | B_577 = '#skF_5'
      | k1_relat_1(B_577) != '#skF_2'
      | ~ v1_funct_1(B_577)
      | ~ v1_relat_1(B_577) ) ),
    inference(resolution,[status(thm)],[c_5169,c_4425])).

tff(c_5650,plain,(
    ! [B_577] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_5',B_577)) = k1_funct_1('#skF_4','#skF_1'('#skF_5',B_577))
      | ~ r1_tarski('#skF_2','#skF_2')
      | B_577 = '#skF_5'
      | k1_relat_1(B_577) != '#skF_2'
      | ~ v1_funct_1(B_577)
      | ~ v1_relat_1(B_577) ) ),
    inference(resolution,[status(thm)],[c_5569,c_44])).

tff(c_6000,plain,(
    ! [B_609] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_5',B_609)) = k1_funct_1('#skF_4','#skF_1'('#skF_5',B_609))
      | B_609 = '#skF_5'
      | k1_relat_1(B_609) != '#skF_2'
      | ~ v1_funct_1(B_609)
      | ~ v1_relat_1(B_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5650])).

tff(c_6006,plain,(
    ! [B_609] :
      ( k1_funct_1(B_609,'#skF_1'('#skF_5',B_609)) != k1_funct_1('#skF_4','#skF_1'('#skF_5',B_609))
      | B_609 = '#skF_5'
      | k1_relat_1(B_609) != k1_relat_1('#skF_5')
      | ~ v1_funct_1(B_609)
      | ~ v1_relat_1(B_609)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | B_609 = '#skF_5'
      | k1_relat_1(B_609) != '#skF_2'
      | ~ v1_funct_1(B_609)
      | ~ v1_relat_1(B_609) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6000,c_18])).

tff(c_6012,plain,(
    ! [B_609] :
      ( k1_funct_1(B_609,'#skF_1'('#skF_5',B_609)) != k1_funct_1('#skF_4','#skF_1'('#skF_5',B_609))
      | B_609 = '#skF_5'
      | k1_relat_1(B_609) != '#skF_2'
      | ~ v1_funct_1(B_609)
      | ~ v1_relat_1(B_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_50,c_5053,c_6006])).

tff(c_6429,plain,
    ( '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6012])).

tff(c_6431,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_56,c_5050,c_6429])).

tff(c_4385,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_4426,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_4385])).

tff(c_6449,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6431,c_4426])).

tff(c_6462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6449])).

tff(c_6494,plain,(
    ! [C_638] :
      ( v1_xboole_0(C_638)
      | ~ m1_subset_1(C_638,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_4461])).

tff(c_6505,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4389,c_6494])).

tff(c_6464,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4461])).

tff(c_6471,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6464,c_10])).

tff(c_6513,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6505,c_6471])).

tff(c_6506,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4388,c_6494])).

tff(c_6520,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6506,c_6471])).

tff(c_6535,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6513,c_6520])).

tff(c_6538,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6535,c_4426])).

tff(c_6547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6538])).

tff(c_6548,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_6569,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_6548])).

tff(c_6573,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6569,c_42])).

tff(c_6552,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_46])).

tff(c_6584,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6569,c_6552])).

tff(c_6972,plain,(
    ! [A_706,B_707,C_708,D_709] :
      ( r2_relset_1(A_706,B_707,C_708,C_708)
      | ~ m1_subset_1(D_709,k1_zfmisc_1(k2_zfmisc_1(A_706,B_707)))
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(A_706,B_707))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6978,plain,(
    ! [C_708,D_709] :
      ( r2_relset_1('#skF_2','#skF_3',C_708,C_708)
      | ~ m1_subset_1(D_709,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4383,c_6972])).

tff(c_6983,plain,(
    ! [C_708,D_709] :
      ( r2_relset_1('#skF_2','#skF_3',C_708,C_708)
      | ~ m1_subset_1(D_709,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_708,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4383,c_6978])).

tff(c_6985,plain,(
    ! [D_709] : ~ m1_subset_1(D_709,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6983])).

tff(c_6987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6985,c_6584])).

tff(c_6989,plain,(
    ! [C_710] :
      ( r2_relset_1('#skF_2','#skF_3',C_710,C_710)
      | ~ m1_subset_1(C_710,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_6983])).

tff(c_6991,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6584,c_6989])).

tff(c_6998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6573,c_6991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.52/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.37  
% 6.72/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.38  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.72/2.38  
% 6.72/2.38  %Foreground sorts:
% 6.72/2.38  
% 6.72/2.38  
% 6.72/2.38  %Background operators:
% 6.72/2.38  
% 6.72/2.38  
% 6.72/2.38  %Foreground operators:
% 6.72/2.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.72/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.72/2.38  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.72/2.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.72/2.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.72/2.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.72/2.38  tff('#skF_5', type, '#skF_5': $i).
% 6.72/2.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.72/2.38  tff('#skF_2', type, '#skF_2': $i).
% 6.72/2.38  tff('#skF_3', type, '#skF_3': $i).
% 6.72/2.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.72/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.72/2.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.72/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.72/2.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.72/2.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.72/2.38  tff('#skF_4', type, '#skF_4': $i).
% 6.72/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.72/2.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.72/2.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.72/2.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.72/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.72/2.38  
% 6.72/2.41  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.72/2.41  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 6.72/2.41  tff(f_79, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.72/2.41  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.72/2.41  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.72/2.41  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.72/2.41  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.72/2.41  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 6.72/2.41  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.72/2.41  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.72/2.41  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.72/2.41  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.72/2.41  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.72/2.41  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_142, plain, (![C_62, B_63, A_64]: (v1_xboole_0(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(B_63, A_64))) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.72/2.41  tff(c_154, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_142])).
% 6.72/2.41  tff(c_156, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_154])).
% 6.72/2.41  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_403, plain, (![A_104, B_105, C_106, D_107]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.72/2.41  tff(c_432, plain, (![C_111]: (r2_relset_1('#skF_2', '#skF_3', C_111, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_46, c_403])).
% 6.72/2.41  tff(c_442, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_432])).
% 6.72/2.41  tff(c_96, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.72/2.41  tff(c_108, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_96])).
% 6.72/2.41  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_172, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.41  tff(c_184, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_172])).
% 6.72/2.41  tff(c_443, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.72/2.41  tff(c_456, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_443])).
% 6.72/2.41  tff(c_464, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_184, c_456])).
% 6.72/2.41  tff(c_468, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_464])).
% 6.72/2.41  tff(c_109, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_96])).
% 6.72/2.41  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_185, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_172])).
% 6.72/2.41  tff(c_459, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_443])).
% 6.72/2.41  tff(c_467, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_185, c_459])).
% 6.72/2.41  tff(c_474, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_467])).
% 6.72/2.41  tff(c_566, plain, (![A_124, B_125]: (r2_hidden('#skF_1'(A_124, B_125), k1_relat_1(A_124)) | B_125=A_124 | k1_relat_1(B_125)!=k1_relat_1(A_124) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.72/2.41  tff(c_571, plain, (![B_125]: (r2_hidden('#skF_1'('#skF_4', B_125), '#skF_2') | B_125='#skF_4' | k1_relat_1(B_125)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_125) | ~v1_relat_1(B_125) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_474, c_566])).
% 6.72/2.41  tff(c_661, plain, (![B_140]: (r2_hidden('#skF_1'('#skF_4', B_140), '#skF_2') | B_140='#skF_4' | k1_relat_1(B_140)!='#skF_2' | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_56, c_474, c_571])).
% 6.72/2.41  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.72/2.41  tff(c_130, plain, (![A_57, C_58, B_59]: (m1_subset_1(A_57, C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.72/2.41  tff(c_137, plain, (![A_57, B_6, A_5]: (m1_subset_1(A_57, B_6) | ~r2_hidden(A_57, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_130])).
% 6.72/2.41  tff(c_1623, plain, (![B_206, B_207]: (m1_subset_1('#skF_1'('#skF_4', B_206), B_207) | ~r1_tarski('#skF_2', B_207) | B_206='#skF_4' | k1_relat_1(B_206)!='#skF_2' | ~v1_funct_1(B_206) | ~v1_relat_1(B_206))), inference(resolution, [status(thm)], [c_661, c_137])).
% 6.72/2.41  tff(c_44, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_4', E_37) | ~m1_subset_1(E_37, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_1685, plain, (![B_206]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_206))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_206)) | ~r1_tarski('#skF_2', '#skF_2') | B_206='#skF_4' | k1_relat_1(B_206)!='#skF_2' | ~v1_funct_1(B_206) | ~v1_relat_1(B_206))), inference(resolution, [status(thm)], [c_1623, c_44])).
% 6.72/2.41  tff(c_2009, plain, (![B_233]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_233))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_233)) | B_233='#skF_4' | k1_relat_1(B_233)!='#skF_2' | ~v1_funct_1(B_233) | ~v1_relat_1(B_233))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1685])).
% 6.72/2.41  tff(c_18, plain, (![B_14, A_10]: (k1_funct_1(B_14, '#skF_1'(A_10, B_14))!=k1_funct_1(A_10, '#skF_1'(A_10, B_14)) | B_14=A_10 | k1_relat_1(B_14)!=k1_relat_1(A_10) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.72/2.41  tff(c_2016, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2009, c_18])).
% 6.72/2.41  tff(c_2023, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50, c_468, c_109, c_56, c_468, c_474, c_2016])).
% 6.72/2.41  tff(c_42, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.72/2.41  tff(c_2036, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2023, c_42])).
% 6.72/2.41  tff(c_2047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_442, c_2036])).
% 6.72/2.41  tff(c_2048, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_467])).
% 6.72/2.41  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.72/2.41  tff(c_2069, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2048, c_2])).
% 6.72/2.41  tff(c_2071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_2069])).
% 6.72/2.41  tff(c_2072, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_464])).
% 6.72/2.41  tff(c_2093, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2072, c_2])).
% 6.72/2.41  tff(c_2095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_2093])).
% 6.72/2.41  tff(c_2097, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_154])).
% 6.72/2.41  tff(c_155, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_142])).
% 6.72/2.41  tff(c_2154, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2097, c_155])).
% 6.72/2.41  tff(c_2277, plain, (![A_245, A_246, B_247]: (v1_xboole_0(A_245) | ~v1_xboole_0(A_246) | ~r1_tarski(A_245, k2_zfmisc_1(B_247, A_246)))), inference(resolution, [status(thm)], [c_14, c_142])).
% 6.72/2.41  tff(c_2290, plain, (![B_248, A_249]: (v1_xboole_0(k2_zfmisc_1(B_248, A_249)) | ~v1_xboole_0(A_249))), inference(resolution, [status(thm)], [c_8, c_2277])).
% 6.72/2.41  tff(c_10, plain, (![B_4, A_3]: (~v1_xboole_0(B_4) | B_4=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.72/2.41  tff(c_2158, plain, (![A_237]: (A_237='#skF_3' | ~v1_xboole_0(A_237))), inference(resolution, [status(thm)], [c_2097, c_10])).
% 6.72/2.41  tff(c_2165, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2154, c_2158])).
% 6.72/2.41  tff(c_59, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | B_39=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.72/2.41  tff(c_62, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_2, c_59])).
% 6.72/2.41  tff(c_2110, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2097, c_62])).
% 6.72/2.41  tff(c_2096, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_154])).
% 6.72/2.41  tff(c_2103, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2096, c_62])).
% 6.72/2.41  tff(c_2133, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2110, c_2103])).
% 6.72/2.41  tff(c_2172, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2165, c_2133])).
% 6.72/2.41  tff(c_2104, plain, (![A_3]: (A_3='#skF_5' | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_2096, c_10])).
% 6.72/2.41  tff(c_2201, plain, (![A_3]: (A_3='#skF_4' | ~v1_xboole_0(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2172, c_2104])).
% 6.72/2.41  tff(c_2298, plain, (![B_250, A_251]: (k2_zfmisc_1(B_250, A_251)='#skF_4' | ~v1_xboole_0(A_251))), inference(resolution, [status(thm)], [c_2290, c_2201])).
% 6.72/2.41  tff(c_2304, plain, (![B_250]: (k2_zfmisc_1(B_250, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_2154, c_2298])).
% 6.72/2.41  tff(c_70, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.72/2.41  tff(c_81, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_70])).
% 6.72/2.41  tff(c_83, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.72/2.41  tff(c_91, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_81, c_83])).
% 6.72/2.41  tff(c_129, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_91])).
% 6.72/2.41  tff(c_2140, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2133, c_129])).
% 6.72/2.41  tff(c_2227, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2165, c_2165, c_2140])).
% 6.72/2.41  tff(c_2307, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2304, c_2227])).
% 6.72/2.41  tff(c_2312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2307])).
% 6.72/2.41  tff(c_2313, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_91])).
% 6.72/2.41  tff(c_2319, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_52])).
% 6.72/2.41  tff(c_2464, plain, (![A_272, B_273, C_274]: (k1_relset_1(A_272, B_273, C_274)=k1_relat_1(C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.41  tff(c_2495, plain, (![C_278]: (k1_relset_1('#skF_2', '#skF_3', C_278)=k1_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2313, c_2464])).
% 6.72/2.41  tff(c_2507, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2319, c_2495])).
% 6.72/2.41  tff(c_2335, plain, (![C_252, B_253, A_254]: (v1_xboole_0(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(B_253, A_254))) | ~v1_xboole_0(A_254))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.72/2.41  tff(c_2338, plain, (![C_252]: (v1_xboole_0(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1('#skF_5')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2313, c_2335])).
% 6.72/2.41  tff(c_2383, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2338])).
% 6.72/2.41  tff(c_2692, plain, (![B_309, C_310, A_311]: (k1_xboole_0=B_309 | v1_funct_2(C_310, A_311, B_309) | k1_relset_1(A_311, B_309, C_310)!=A_311 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_311, B_309))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.72/2.41  tff(c_2701, plain, (![C_310]: (k1_xboole_0='#skF_3' | v1_funct_2(C_310, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_310)!='#skF_2' | ~m1_subset_1(C_310, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2313, c_2692])).
% 6.72/2.41  tff(c_2807, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2701])).
% 6.72/2.41  tff(c_2831, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2807, c_2])).
% 6.72/2.41  tff(c_2833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2383, c_2831])).
% 6.72/2.41  tff(c_2835, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2701])).
% 6.72/2.41  tff(c_2852, plain, (![B_330, A_331, C_332]: (k1_xboole_0=B_330 | k1_relset_1(A_331, B_330, C_332)=A_331 | ~v1_funct_2(C_332, A_331, B_330) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.72/2.41  tff(c_2861, plain, (![C_332]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_332)='#skF_2' | ~v1_funct_2(C_332, '#skF_2', '#skF_3') | ~m1_subset_1(C_332, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2313, c_2852])).
% 6.72/2.41  tff(c_2887, plain, (![C_336]: (k1_relset_1('#skF_2', '#skF_3', C_336)='#skF_2' | ~v1_funct_2(C_336, '#skF_2', '#skF_3') | ~m1_subset_1(C_336, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2835, c_2861])).
% 6.72/2.41  tff(c_2893, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2319, c_2887])).
% 6.72/2.41  tff(c_2903, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2507, c_2893])).
% 6.72/2.41  tff(c_2318, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_46])).
% 6.72/2.41  tff(c_2506, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2318, c_2495])).
% 6.72/2.41  tff(c_2890, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2318, c_2887])).
% 6.72/2.41  tff(c_2900, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2506, c_2890])).
% 6.72/2.41  tff(c_2919, plain, (![A_337, B_338]: (r2_hidden('#skF_1'(A_337, B_338), k1_relat_1(A_337)) | B_338=A_337 | k1_relat_1(B_338)!=k1_relat_1(A_337) | ~v1_funct_1(B_338) | ~v1_relat_1(B_338) | ~v1_funct_1(A_337) | ~v1_relat_1(A_337))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.72/2.41  tff(c_2927, plain, (![B_338]: (r2_hidden('#skF_1'('#skF_5', B_338), '#skF_2') | B_338='#skF_5' | k1_relat_1(B_338)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_338) | ~v1_relat_1(B_338) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2900, c_2919])).
% 6.72/2.41  tff(c_2966, plain, (![B_341]: (r2_hidden('#skF_1'('#skF_5', B_341), '#skF_2') | B_341='#skF_5' | k1_relat_1(B_341)!='#skF_2' | ~v1_funct_1(B_341) | ~v1_relat_1(B_341))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50, c_2900, c_2927])).
% 6.72/2.41  tff(c_2384, plain, (![A_257, C_258, B_259]: (m1_subset_1(A_257, C_258) | ~m1_subset_1(B_259, k1_zfmisc_1(C_258)) | ~r2_hidden(A_257, B_259))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.72/2.41  tff(c_2393, plain, (![A_257, B_6, A_5]: (m1_subset_1(A_257, B_6) | ~r2_hidden(A_257, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_2384])).
% 6.72/2.41  tff(c_3461, plain, (![B_378, B_379]: (m1_subset_1('#skF_1'('#skF_5', B_378), B_379) | ~r1_tarski('#skF_2', B_379) | B_378='#skF_5' | k1_relat_1(B_378)!='#skF_2' | ~v1_funct_1(B_378) | ~v1_relat_1(B_378))), inference(resolution, [status(thm)], [c_2966, c_2393])).
% 6.72/2.41  tff(c_3539, plain, (![B_378]: (k1_funct_1('#skF_5', '#skF_1'('#skF_5', B_378))=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_378)) | ~r1_tarski('#skF_2', '#skF_2') | B_378='#skF_5' | k1_relat_1(B_378)!='#skF_2' | ~v1_funct_1(B_378) | ~v1_relat_1(B_378))), inference(resolution, [status(thm)], [c_3461, c_44])).
% 6.72/2.41  tff(c_3883, plain, (![B_407]: (k1_funct_1('#skF_5', '#skF_1'('#skF_5', B_407))=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_407)) | B_407='#skF_5' | k1_relat_1(B_407)!='#skF_2' | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3539])).
% 6.72/2.41  tff(c_3889, plain, (![B_407]: (k1_funct_1(B_407, '#skF_1'('#skF_5', B_407))!=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_407)) | B_407='#skF_5' | k1_relat_1(B_407)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_407) | ~v1_relat_1(B_407) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | B_407='#skF_5' | k1_relat_1(B_407)!='#skF_2' | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(superposition, [status(thm), theory('equality')], [c_3883, c_18])).
% 6.72/2.41  tff(c_3895, plain, (![B_407]: (k1_funct_1(B_407, '#skF_1'('#skF_5', B_407))!=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_407)) | B_407='#skF_5' | k1_relat_1(B_407)!='#skF_2' | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50, c_2900, c_3889])).
% 6.72/2.41  tff(c_4225, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_3895])).
% 6.72/2.41  tff(c_4227, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_56, c_2903, c_4225])).
% 6.72/2.41  tff(c_82, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_70])).
% 6.72/2.41  tff(c_90, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_82, c_83])).
% 6.72/2.41  tff(c_128, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_90])).
% 6.72/2.41  tff(c_2315, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_128])).
% 6.72/2.41  tff(c_4258, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4227, c_2315])).
% 6.72/2.41  tff(c_4271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_4258])).
% 6.72/2.41  tff(c_4306, plain, (![C_443]: (v1_xboole_0(C_443) | ~m1_subset_1(C_443, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_2338])).
% 6.72/2.41  tff(c_4318, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2319, c_4306])).
% 6.72/2.41  tff(c_4273, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_2338])).
% 6.72/2.41  tff(c_4280, plain, (![A_3]: (A_3='#skF_3' | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_4273, c_10])).
% 6.72/2.41  tff(c_4332, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4318, c_4280])).
% 6.72/2.41  tff(c_4317, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2318, c_4306])).
% 6.72/2.41  tff(c_4325, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_4317, c_4280])).
% 6.72/2.41  tff(c_4342, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4325, c_2315])).
% 6.72/2.41  tff(c_4382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_4332, c_4342])).
% 6.72/2.41  tff(c_4383, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_90])).
% 6.72/2.41  tff(c_4389, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_52])).
% 6.72/2.41  tff(c_4493, plain, (![A_464, B_465, C_466]: (k1_relset_1(A_464, B_465, C_466)=k1_relat_1(C_466) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.41  tff(c_4576, plain, (![C_479]: (k1_relset_1('#skF_2', '#skF_3', C_479)=k1_relat_1(C_479) | ~m1_subset_1(C_479, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4383, c_4493])).
% 6.72/2.41  tff(c_4587, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4389, c_4576])).
% 6.72/2.41  tff(c_4458, plain, (![C_455, B_456, A_457]: (v1_xboole_0(C_455) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(B_456, A_457))) | ~v1_xboole_0(A_457))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.72/2.41  tff(c_4461, plain, (![C_455]: (v1_xboole_0(C_455) | ~m1_subset_1(C_455, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4383, c_4458])).
% 6.72/2.41  tff(c_4467, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_4461])).
% 6.72/2.41  tff(c_4923, plain, (![B_527, C_528, A_529]: (k1_xboole_0=B_527 | v1_funct_2(C_528, A_529, B_527) | k1_relset_1(A_529, B_527, C_528)!=A_529 | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_529, B_527))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.72/2.41  tff(c_4932, plain, (![C_528]: (k1_xboole_0='#skF_3' | v1_funct_2(C_528, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_528)!='#skF_2' | ~m1_subset_1(C_528, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4383, c_4923])).
% 6.72/2.41  tff(c_4957, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4932])).
% 6.72/2.41  tff(c_4985, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4957, c_2])).
% 6.72/2.41  tff(c_4987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4467, c_4985])).
% 6.72/2.41  tff(c_4989, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4932])).
% 6.72/2.41  tff(c_4799, plain, (![B_506, A_507, C_508]: (k1_xboole_0=B_506 | k1_relset_1(A_507, B_506, C_508)=A_507 | ~v1_funct_2(C_508, A_507, B_506) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_507, B_506))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.72/2.41  tff(c_4808, plain, (![C_508]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_508)='#skF_2' | ~v1_funct_2(C_508, '#skF_2', '#skF_3') | ~m1_subset_1(C_508, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4383, c_4799])).
% 6.72/2.41  tff(c_5037, plain, (![C_542]: (k1_relset_1('#skF_2', '#skF_3', C_542)='#skF_2' | ~v1_funct_2(C_542, '#skF_2', '#skF_3') | ~m1_subset_1(C_542, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_4989, c_4808])).
% 6.72/2.41  tff(c_5040, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_4389, c_5037])).
% 6.72/2.41  tff(c_5050, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4587, c_5040])).
% 6.72/2.41  tff(c_4388, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_46])).
% 6.72/2.41  tff(c_4588, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4388, c_4576])).
% 6.72/2.41  tff(c_5043, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_4388, c_5037])).
% 6.72/2.41  tff(c_5053, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4588, c_5043])).
% 6.72/2.41  tff(c_20, plain, (![A_10, B_14]: (r2_hidden('#skF_1'(A_10, B_14), k1_relat_1(A_10)) | B_14=A_10 | k1_relat_1(B_14)!=k1_relat_1(A_10) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.72/2.41  tff(c_5069, plain, (![B_14]: (r2_hidden('#skF_1'('#skF_5', B_14), '#skF_2') | B_14='#skF_5' | k1_relat_1(B_14)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5053, c_20])).
% 6.72/2.41  tff(c_5169, plain, (![B_550]: (r2_hidden('#skF_1'('#skF_5', B_550), '#skF_2') | B_550='#skF_5' | k1_relat_1(B_550)!='#skF_2' | ~v1_funct_1(B_550) | ~v1_relat_1(B_550))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50, c_5053, c_5069])).
% 6.72/2.41  tff(c_4416, plain, (![A_445, C_446, B_447]: (m1_subset_1(A_445, C_446) | ~m1_subset_1(B_447, k1_zfmisc_1(C_446)) | ~r2_hidden(A_445, B_447))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.72/2.41  tff(c_4425, plain, (![A_445, B_6, A_5]: (m1_subset_1(A_445, B_6) | ~r2_hidden(A_445, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_4416])).
% 6.72/2.41  tff(c_5569, plain, (![B_577, B_578]: (m1_subset_1('#skF_1'('#skF_5', B_577), B_578) | ~r1_tarski('#skF_2', B_578) | B_577='#skF_5' | k1_relat_1(B_577)!='#skF_2' | ~v1_funct_1(B_577) | ~v1_relat_1(B_577))), inference(resolution, [status(thm)], [c_5169, c_4425])).
% 6.72/2.41  tff(c_5650, plain, (![B_577]: (k1_funct_1('#skF_5', '#skF_1'('#skF_5', B_577))=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_577)) | ~r1_tarski('#skF_2', '#skF_2') | B_577='#skF_5' | k1_relat_1(B_577)!='#skF_2' | ~v1_funct_1(B_577) | ~v1_relat_1(B_577))), inference(resolution, [status(thm)], [c_5569, c_44])).
% 6.72/2.41  tff(c_6000, plain, (![B_609]: (k1_funct_1('#skF_5', '#skF_1'('#skF_5', B_609))=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_609)) | B_609='#skF_5' | k1_relat_1(B_609)!='#skF_2' | ~v1_funct_1(B_609) | ~v1_relat_1(B_609))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5650])).
% 6.72/2.41  tff(c_6006, plain, (![B_609]: (k1_funct_1(B_609, '#skF_1'('#skF_5', B_609))!=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_609)) | B_609='#skF_5' | k1_relat_1(B_609)!=k1_relat_1('#skF_5') | ~v1_funct_1(B_609) | ~v1_relat_1(B_609) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | B_609='#skF_5' | k1_relat_1(B_609)!='#skF_2' | ~v1_funct_1(B_609) | ~v1_relat_1(B_609))), inference(superposition, [status(thm), theory('equality')], [c_6000, c_18])).
% 6.72/2.41  tff(c_6012, plain, (![B_609]: (k1_funct_1(B_609, '#skF_1'('#skF_5', B_609))!=k1_funct_1('#skF_4', '#skF_1'('#skF_5', B_609)) | B_609='#skF_5' | k1_relat_1(B_609)!='#skF_2' | ~v1_funct_1(B_609) | ~v1_relat_1(B_609))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_50, c_5053, c_6006])).
% 6.72/2.41  tff(c_6429, plain, ('#skF_5'='#skF_4' | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_6012])).
% 6.72/2.41  tff(c_6431, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_56, c_5050, c_6429])).
% 6.72/2.41  tff(c_4385, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_91])).
% 6.72/2.41  tff(c_4426, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_4385])).
% 6.72/2.41  tff(c_6449, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6431, c_4426])).
% 6.72/2.41  tff(c_6462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6449])).
% 6.72/2.41  tff(c_6494, plain, (![C_638]: (v1_xboole_0(C_638) | ~m1_subset_1(C_638, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_4461])).
% 6.72/2.41  tff(c_6505, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4389, c_6494])).
% 6.72/2.41  tff(c_6464, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_4461])).
% 6.72/2.41  tff(c_6471, plain, (![A_3]: (A_3='#skF_3' | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6464, c_10])).
% 6.72/2.41  tff(c_6513, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_6505, c_6471])).
% 6.72/2.41  tff(c_6506, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4388, c_6494])).
% 6.72/2.41  tff(c_6520, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_6506, c_6471])).
% 6.72/2.41  tff(c_6535, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6513, c_6520])).
% 6.72/2.41  tff(c_6538, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6535, c_4426])).
% 6.72/2.41  tff(c_6547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6538])).
% 6.72/2.41  tff(c_6548, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_91])).
% 6.72/2.41  tff(c_6569, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_6548])).
% 6.72/2.41  tff(c_6573, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6569, c_42])).
% 6.72/2.41  tff(c_6552, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_46])).
% 6.72/2.41  tff(c_6584, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6569, c_6552])).
% 6.72/2.41  tff(c_6972, plain, (![A_706, B_707, C_708, D_709]: (r2_relset_1(A_706, B_707, C_708, C_708) | ~m1_subset_1(D_709, k1_zfmisc_1(k2_zfmisc_1(A_706, B_707))) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(A_706, B_707))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.72/2.41  tff(c_6978, plain, (![C_708, D_709]: (r2_relset_1('#skF_2', '#skF_3', C_708, C_708) | ~m1_subset_1(D_709, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_4383, c_6972])).
% 6.72/2.41  tff(c_6983, plain, (![C_708, D_709]: (r2_relset_1('#skF_2', '#skF_3', C_708, C_708) | ~m1_subset_1(D_709, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_708, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4383, c_6978])).
% 6.72/2.41  tff(c_6985, plain, (![D_709]: (~m1_subset_1(D_709, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_6983])).
% 6.72/2.41  tff(c_6987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6985, c_6584])).
% 6.72/2.41  tff(c_6989, plain, (![C_710]: (r2_relset_1('#skF_2', '#skF_3', C_710, C_710) | ~m1_subset_1(C_710, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_6983])).
% 6.72/2.41  tff(c_6991, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_6584, c_6989])).
% 6.72/2.41  tff(c_6998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6573, c_6991])).
% 6.72/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.41  
% 6.72/2.41  Inference rules
% 6.72/2.41  ----------------------
% 6.72/2.41  #Ref     : 5
% 6.72/2.41  #Sup     : 1640
% 6.72/2.41  #Fact    : 0
% 6.72/2.41  #Define  : 0
% 6.72/2.41  #Split   : 28
% 6.72/2.41  #Chain   : 0
% 6.72/2.41  #Close   : 0
% 6.72/2.41  
% 6.72/2.41  Ordering : KBO
% 6.72/2.41  
% 6.72/2.41  Simplification rules
% 6.72/2.41  ----------------------
% 6.72/2.41  #Subsume      : 466
% 6.72/2.41  #Demod        : 1201
% 6.72/2.41  #Tautology    : 496
% 6.72/2.41  #SimpNegUnit  : 62
% 6.72/2.41  #BackRed      : 252
% 6.72/2.41  
% 6.72/2.41  #Partial instantiations: 0
% 6.72/2.41  #Strategies tried      : 1
% 6.72/2.41  
% 6.72/2.41  Timing (in seconds)
% 6.72/2.41  ----------------------
% 6.72/2.41  Preprocessing        : 0.34
% 6.72/2.41  Parsing              : 0.19
% 6.72/2.41  CNF conversion       : 0.02
% 6.72/2.41  Main loop            : 1.24
% 6.72/2.41  Inferencing          : 0.41
% 6.72/2.41  Reduction            : 0.38
% 6.72/2.41  Demodulation         : 0.26
% 6.72/2.41  BG Simplification    : 0.05
% 6.72/2.41  Subsumption          : 0.30
% 6.72/2.41  Abstraction          : 0.05
% 6.72/2.41  MUC search           : 0.00
% 6.72/2.41  Cooper               : 0.00
% 6.72/2.41  Total                : 1.65
% 6.72/2.41  Index Insertion      : 0.00
% 6.72/2.41  Index Deletion       : 0.00
% 6.72/2.41  Index Matching       : 0.00
% 6.72/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
