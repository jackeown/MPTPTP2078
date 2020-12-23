%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:20 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 292 expanded)
%              Number of leaves         :   34 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 956 expanded)
%              Number of equality atoms :   58 ( 267 expanded)
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

tff(f_130,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_75,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2651,plain,(
    ! [A_164,B_165,D_166] :
      ( r2_relset_1(A_164,B_165,D_166,D_166)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2660,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_2651])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_relset_1(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_214,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_106,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_118,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_106])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_371,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_390,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_371])).

tff(c_463,plain,(
    ! [B_98,A_99,C_100] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(A_99,B_98,C_100) = A_99
      | ~ v1_funct_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_477,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_463])).

tff(c_491,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_390,c_477])).

tff(c_501,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_117,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_106])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_389,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_371])).

tff(c_474,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_463])).

tff(c_488,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_389,c_474])).

tff(c_495,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_1790,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_2'(A_121,B_122),k1_relat_1(A_121))
      | B_122 = A_121
      | k1_relat_1(B_122) != k1_relat_1(A_121)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1805,plain,(
    ! [B_122] :
      ( r2_hidden('#skF_2'('#skF_6',B_122),'#skF_3')
      | B_122 = '#skF_6'
      | k1_relat_1(B_122) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_1790])).

tff(c_1827,plain,(
    ! [B_124] :
      ( r2_hidden('#skF_2'('#skF_6',B_124),'#skF_3')
      | B_124 = '#skF_6'
      | k1_relat_1(B_124) != '#skF_3'
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_52,c_495,c_1805])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1851,plain,(
    ! [B_128] :
      ( m1_subset_1('#skF_2'('#skF_6',B_128),'#skF_3')
      | B_128 = '#skF_6'
      | k1_relat_1(B_128) != '#skF_3'
      | ~ v1_funct_1(B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_1827,c_16])).

tff(c_46,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_6',E_37)
      | ~ m1_subset_1(E_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2288,plain,(
    ! [B_146] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_146)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_146))
      | B_146 = '#skF_6'
      | k1_relat_1(B_146) != '#skF_3'
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_1851,c_46])).

tff(c_20,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_2'(A_14,B_18)) != k1_funct_1(A_14,'#skF_2'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2295,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2288,c_20])).

tff(c_2302,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_58,c_501,c_117,c_52,c_501,c_495,c_2295])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2315,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2302,c_44])).

tff(c_2325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2315])).

tff(c_2326,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2349,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2347,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_12])).

tff(c_171,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_184,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_59,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_171])).

tff(c_186,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_2423,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_186])).

tff(c_2428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2349,c_2423])).

tff(c_2429,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_2452,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_6])).

tff(c_2450,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_2429,c_12])).

tff(c_2492,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2450,c_186])).

tff(c_2497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2452,c_2492])).

tff(c_2500,plain,(
    ! [A_155] : ~ r2_hidden(A_155,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2505,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_2500])).

tff(c_2499,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_185,plain,(
    ! [A_59] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_59,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_171])).

tff(c_2631,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_2636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_2631])).

tff(c_2639,plain,(
    ! [A_163] : ~ r2_hidden(A_163,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_2644,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2639])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2663,plain,(
    ! [A_167] :
      ( A_167 = '#skF_5'
      | ~ v1_xboole_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_2644,c_8])).

tff(c_2676,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2505,c_2663])).

tff(c_2683,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2676,c_44])).

tff(c_2775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2660,c_2683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.88  
% 4.78/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.88  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.78/1.88  
% 4.78/1.88  %Foreground sorts:
% 4.78/1.88  
% 4.78/1.88  
% 4.78/1.88  %Background operators:
% 4.78/1.88  
% 4.78/1.88  
% 4.78/1.88  %Foreground operators:
% 4.78/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.78/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.88  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.78/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.78/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.78/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.78/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.78/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.78/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.78/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.78/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/1.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.78/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.78/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.78/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.78/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.78/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.78/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.78/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.88  
% 4.78/1.89  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 4.78/1.89  tff(f_91, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.78/1.89  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.78/1.89  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.78/1.89  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.78/1.89  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.78/1.89  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.78/1.89  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.78/1.89  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.78/1.89  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.78/1.89  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.78/1.89  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.78/1.89  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_2651, plain, (![A_164, B_165, D_166]: (r2_relset_1(A_164, B_165, D_166, D_166) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.89  tff(c_2660, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_2651])).
% 4.78/1.89  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.78/1.89  tff(c_201, plain, (![A_63, B_64, D_65]: (r2_relset_1(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.89  tff(c_214, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_201])).
% 4.78/1.89  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_106, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.78/1.89  tff(c_118, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_106])).
% 4.78/1.89  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_371, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.78/1.89  tff(c_390, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_371])).
% 4.78/1.89  tff(c_463, plain, (![B_98, A_99, C_100]: (k1_xboole_0=B_98 | k1_relset_1(A_99, B_98, C_100)=A_99 | ~v1_funct_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.78/1.89  tff(c_477, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_463])).
% 4.78/1.89  tff(c_491, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_390, c_477])).
% 4.78/1.89  tff(c_501, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_491])).
% 4.78/1.89  tff(c_117, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_106])).
% 4.78/1.89  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_389, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_371])).
% 4.78/1.89  tff(c_474, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_463])).
% 4.78/1.89  tff(c_488, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_389, c_474])).
% 4.78/1.89  tff(c_495, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_488])).
% 4.78/1.89  tff(c_1790, plain, (![A_121, B_122]: (r2_hidden('#skF_2'(A_121, B_122), k1_relat_1(A_121)) | B_122=A_121 | k1_relat_1(B_122)!=k1_relat_1(A_121) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.78/1.89  tff(c_1805, plain, (![B_122]: (r2_hidden('#skF_2'('#skF_6', B_122), '#skF_3') | B_122='#skF_6' | k1_relat_1(B_122)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_122) | ~v1_relat_1(B_122) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_495, c_1790])).
% 4.78/1.89  tff(c_1827, plain, (![B_124]: (r2_hidden('#skF_2'('#skF_6', B_124), '#skF_3') | B_124='#skF_6' | k1_relat_1(B_124)!='#skF_3' | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_52, c_495, c_1805])).
% 4.78/1.89  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.78/1.89  tff(c_1851, plain, (![B_128]: (m1_subset_1('#skF_2'('#skF_6', B_128), '#skF_3') | B_128='#skF_6' | k1_relat_1(B_128)!='#skF_3' | ~v1_funct_1(B_128) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_1827, c_16])).
% 4.78/1.89  tff(c_46, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_6', E_37) | ~m1_subset_1(E_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_2288, plain, (![B_146]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_146))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_146)) | B_146='#skF_6' | k1_relat_1(B_146)!='#skF_3' | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_1851, c_46])).
% 4.78/1.89  tff(c_20, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_2'(A_14, B_18))!=k1_funct_1(A_14, '#skF_2'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.78/1.89  tff(c_2295, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2288, c_20])).
% 4.78/1.89  tff(c_2302, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_58, c_501, c_117, c_52, c_501, c_495, c_2295])).
% 4.78/1.89  tff(c_44, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.78/1.89  tff(c_2315, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2302, c_44])).
% 4.78/1.89  tff(c_2325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_2315])).
% 4.78/1.89  tff(c_2326, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_491])).
% 4.78/1.89  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.78/1.89  tff(c_2349, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_6])).
% 4.78/1.89  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.78/1.89  tff(c_2347, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_12])).
% 4.78/1.89  tff(c_171, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.78/1.89  tff(c_184, plain, (![A_59]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_59, '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_171])).
% 4.78/1.89  tff(c_186, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_184])).
% 4.78/1.89  tff(c_2423, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_186])).
% 4.78/1.89  tff(c_2428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2349, c_2423])).
% 4.78/1.89  tff(c_2429, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_488])).
% 4.78/1.89  tff(c_2452, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_6])).
% 4.78/1.89  tff(c_2450, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_2429, c_12])).
% 4.78/1.89  tff(c_2492, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2450, c_186])).
% 4.78/1.89  tff(c_2497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2452, c_2492])).
% 4.78/1.89  tff(c_2500, plain, (![A_155]: (~r2_hidden(A_155, '#skF_6'))), inference(splitRight, [status(thm)], [c_184])).
% 4.78/1.89  tff(c_2505, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_2500])).
% 4.78/1.89  tff(c_2499, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_184])).
% 4.78/1.89  tff(c_185, plain, (![A_59]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_59, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_171])).
% 4.78/1.89  tff(c_2631, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_185])).
% 4.78/1.89  tff(c_2636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2499, c_2631])).
% 4.78/1.89  tff(c_2639, plain, (![A_163]: (~r2_hidden(A_163, '#skF_5'))), inference(splitRight, [status(thm)], [c_185])).
% 4.78/1.89  tff(c_2644, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_2639])).
% 4.78/1.89  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.78/1.89  tff(c_2663, plain, (![A_167]: (A_167='#skF_5' | ~v1_xboole_0(A_167))), inference(resolution, [status(thm)], [c_2644, c_8])).
% 4.78/1.89  tff(c_2676, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2505, c_2663])).
% 4.78/1.89  tff(c_2683, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2676, c_44])).
% 4.78/1.89  tff(c_2775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2660, c_2683])).
% 4.78/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.89  
% 4.78/1.89  Inference rules
% 4.78/1.89  ----------------------
% 4.78/1.89  #Ref     : 1
% 4.78/1.89  #Sup     : 720
% 4.78/1.89  #Fact    : 5
% 4.78/1.89  #Define  : 0
% 4.78/1.89  #Split   : 11
% 4.78/1.89  #Chain   : 0
% 4.78/1.89  #Close   : 0
% 4.78/1.89  
% 4.78/1.89  Ordering : KBO
% 4.78/1.89  
% 4.78/1.89  Simplification rules
% 4.78/1.89  ----------------------
% 4.78/1.89  #Subsume      : 338
% 4.78/1.89  #Demod        : 410
% 4.78/1.89  #Tautology    : 191
% 4.78/1.89  #SimpNegUnit  : 3
% 4.78/1.89  #BackRed      : 105
% 4.78/1.89  
% 4.78/1.89  #Partial instantiations: 0
% 4.78/1.89  #Strategies tried      : 1
% 4.78/1.89  
% 4.78/1.89  Timing (in seconds)
% 4.78/1.89  ----------------------
% 4.78/1.90  Preprocessing        : 0.32
% 4.78/1.90  Parsing              : 0.16
% 4.78/1.90  CNF conversion       : 0.02
% 4.78/1.90  Main loop            : 0.77
% 4.78/1.90  Inferencing          : 0.23
% 4.78/1.90  Reduction            : 0.22
% 4.78/1.90  Demodulation         : 0.16
% 4.78/1.90  BG Simplification    : 0.03
% 4.78/1.90  Subsumption          : 0.25
% 4.78/1.90  Abstraction          : 0.04
% 4.78/1.90  MUC search           : 0.00
% 4.78/1.90  Cooper               : 0.00
% 4.78/1.90  Total                : 1.13
% 4.78/1.90  Index Insertion      : 0.00
% 4.78/1.90  Index Deletion       : 0.00
% 4.78/1.90  Index Matching       : 0.00
% 4.78/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
