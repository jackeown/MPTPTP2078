%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 930 expanded)
%              Number of leaves         :   34 ( 323 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 (2087 expanded)
%              Number of equality atoms :   50 ( 596 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_41,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_56,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2954,plain,(
    ! [A_286] :
      ( r1_tarski(A_286,k2_zfmisc_1(k1_relat_1(A_286),k2_relat_1(A_286)))
      | ~ v1_relat_1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2855,plain,(
    ! [A_263,B_264] :
      ( m1_subset_1(A_263,k1_zfmisc_1(B_264))
      | ~ r1_tarski(A_263,B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_108,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_118,plain,(
    ! [C_52] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_108])).

tff(c_128,plain,(
    ! [A_55] :
      ( v1_relat_1(A_55)
      | ~ r1_tarski(A_55,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_118])).

tff(c_138,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_206,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_269,plain,(
    ! [A_98,A_99,B_100] :
      ( v4_relat_1(A_98,A_99)
      | ~ r1_tarski(A_98,k2_zfmisc_1(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_16,c_206])).

tff(c_290,plain,(
    ! [A_101,B_102] : v4_relat_1(k2_zfmisc_1(A_101,B_102),A_101) ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_303,plain,(
    ! [A_103] : v4_relat_1(k1_xboole_0,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_290])).

tff(c_18,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = B_8
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_306,plain,(
    ! [A_103] :
      ( k7_relat_1(k1_xboole_0,A_103) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_303,c_18])).

tff(c_352,plain,(
    ! [A_107] : k7_relat_1(k1_xboole_0,A_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_306])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_361,plain,(
    ! [A_107] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),A_107)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_22])).

tff(c_370,plain,(
    ! [A_108] : r1_tarski(k1_relat_1(k1_xboole_0),A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_361])).

tff(c_88,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_1'(A_41),A_41)
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [A_41] :
      ( ~ r1_tarski(A_41,'#skF_1'(A_41))
      | k1_xboole_0 = A_41 ) ),
    inference(resolution,[status(thm)],[c_88,c_24])).

tff(c_400,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_370,c_92])).

tff(c_368,plain,(
    ! [A_107] : r1_tarski(k1_relat_1(k1_xboole_0),A_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_361])).

tff(c_401,plain,(
    ! [A_107] : r1_tarski(k1_xboole_0,A_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_368])).

tff(c_20,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_322,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_950,plain,(
    ! [A_170,B_171,A_172] :
      ( k1_relset_1(A_170,B_171,A_172) = k1_relat_1(A_172)
      | ~ r1_tarski(A_172,k2_zfmisc_1(A_170,B_171)) ) ),
    inference(resolution,[status(thm)],[c_16,c_322])).

tff(c_979,plain,(
    ! [A_9] :
      ( k1_relset_1(k1_relat_1(A_9),k2_relat_1(A_9),A_9) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_20,c_950])).

tff(c_450,plain,(
    ! [B_111,C_112,A_113] :
      ( k1_xboole_0 = B_111
      | v1_funct_2(C_112,A_113,B_111)
      | k1_relset_1(A_113,B_111,C_112) != A_113
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1635,plain,(
    ! [B_216,A_217,A_218] :
      ( k1_xboole_0 = B_216
      | v1_funct_2(A_217,A_218,B_216)
      | k1_relset_1(A_218,B_216,A_217) != A_218
      | ~ r1_tarski(A_217,k2_zfmisc_1(A_218,B_216)) ) ),
    inference(resolution,[status(thm)],[c_16,c_450])).

tff(c_2328,plain,(
    ! [A_251] :
      ( k2_relat_1(A_251) = k1_xboole_0
      | v1_funct_2(A_251,k1_relat_1(A_251),k2_relat_1(A_251))
      | k1_relset_1(k1_relat_1(A_251),k2_relat_1(A_251),A_251) != k1_relat_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(resolution,[status(thm)],[c_20,c_1635])).

tff(c_54,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_95,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_2335,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2328,c_95])).

tff(c_2353,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2335])).

tff(c_2356,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2353])).

tff(c_2359,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_2356])).

tff(c_2363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2359])).

tff(c_2364,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2353])).

tff(c_174,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66)))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_66] :
      ( k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66)) = A_66
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66)),A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_2373,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2364,c_181])).

tff(c_2388,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_401,c_10,c_10,c_2364,c_2373])).

tff(c_40,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_61,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_310,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_314,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_310])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_314])).

tff(c_320,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_750,plain,(
    ! [B_146,C_147] :
      ( k1_relset_1(k1_xboole_0,B_146,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_322])).

tff(c_752,plain,(
    ! [B_146] : k1_relset_1(k1_xboole_0,B_146,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_320,c_750])).

tff(c_757,plain,(
    ! [B_146] : k1_relset_1(k1_xboole_0,B_146,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_752])).

tff(c_44,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_734,plain,(
    ! [C_143,B_144] :
      ( v1_funct_2(C_143,k1_xboole_0,B_144)
      | k1_relset_1(k1_xboole_0,B_144,C_143) != k1_xboole_0
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_740,plain,(
    ! [B_144] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_144)
      | k1_relset_1(k1_xboole_0,B_144,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_320,c_734])).

tff(c_760,plain,(
    ! [B_144] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_740])).

tff(c_2425,plain,(
    ! [B_144] : v1_funct_2('#skF_2','#skF_2',B_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2388,c_760])).

tff(c_2438,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2388,c_400])).

tff(c_2366,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_95])).

tff(c_2396,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2388,c_2366])).

tff(c_2592,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_2396])).

tff(c_2852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_2592])).

tff(c_2853,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2862,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2855,c_2853])).

tff(c_2962,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2954,c_2862])).

tff(c_2968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.87  
% 4.26/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 4.26/1.88  
% 4.26/1.88  %Foreground sorts:
% 4.26/1.88  
% 4.26/1.88  
% 4.26/1.88  %Background operators:
% 4.26/1.88  
% 4.26/1.88  
% 4.26/1.88  %Foreground operators:
% 4.26/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.26/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.26/1.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.26/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.26/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.26/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.26/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.26/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.26/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.88  
% 4.26/1.89  tff(f_119, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.26/1.89  tff(f_51, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.26/1.89  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.26/1.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.26/1.89  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.26/1.89  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.26/1.89  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.26/1.89  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.26/1.89  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 4.26/1.89  tff(f_90, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.26/1.89  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.26/1.89  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.26/1.89  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.26/1.89  tff(c_56, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.26/1.89  tff(c_2954, plain, (![A_286]: (r1_tarski(A_286, k2_zfmisc_1(k1_relat_1(A_286), k2_relat_1(A_286))) | ~v1_relat_1(A_286))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.26/1.89  tff(c_2855, plain, (![A_263, B_264]: (m1_subset_1(A_263, k1_zfmisc_1(B_264)) | ~r1_tarski(A_263, B_264))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.26/1.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.89  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.26/1.89  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.89  tff(c_108, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.26/1.89  tff(c_118, plain, (![C_52]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_108])).
% 4.26/1.89  tff(c_128, plain, (![A_55]: (v1_relat_1(A_55) | ~r1_tarski(A_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_118])).
% 4.26/1.89  tff(c_138, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.26/1.89  tff(c_206, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.26/1.89  tff(c_269, plain, (![A_98, A_99, B_100]: (v4_relat_1(A_98, A_99) | ~r1_tarski(A_98, k2_zfmisc_1(A_99, B_100)))), inference(resolution, [status(thm)], [c_16, c_206])).
% 4.26/1.89  tff(c_290, plain, (![A_101, B_102]: (v4_relat_1(k2_zfmisc_1(A_101, B_102), A_101))), inference(resolution, [status(thm)], [c_6, c_269])).
% 4.26/1.89  tff(c_303, plain, (![A_103]: (v4_relat_1(k1_xboole_0, A_103))), inference(superposition, [status(thm), theory('equality')], [c_10, c_290])).
% 4.26/1.89  tff(c_18, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=B_8 | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.26/1.89  tff(c_306, plain, (![A_103]: (k7_relat_1(k1_xboole_0, A_103)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_303, c_18])).
% 4.26/1.89  tff(c_352, plain, (![A_107]: (k7_relat_1(k1_xboole_0, A_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_306])).
% 4.26/1.89  tff(c_22, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.26/1.89  tff(c_361, plain, (![A_107]: (r1_tarski(k1_relat_1(k1_xboole_0), A_107) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_352, c_22])).
% 4.26/1.89  tff(c_370, plain, (![A_108]: (r1_tarski(k1_relat_1(k1_xboole_0), A_108))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_361])).
% 4.26/1.89  tff(c_88, plain, (![A_41]: (r2_hidden('#skF_1'(A_41), A_41) | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.26/1.89  tff(c_24, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.26/1.89  tff(c_92, plain, (![A_41]: (~r1_tarski(A_41, '#skF_1'(A_41)) | k1_xboole_0=A_41)), inference(resolution, [status(thm)], [c_88, c_24])).
% 4.26/1.89  tff(c_400, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_370, c_92])).
% 4.26/1.89  tff(c_368, plain, (![A_107]: (r1_tarski(k1_relat_1(k1_xboole_0), A_107))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_361])).
% 4.26/1.89  tff(c_401, plain, (![A_107]: (r1_tarski(k1_xboole_0, A_107))), inference(demodulation, [status(thm), theory('equality')], [c_400, c_368])).
% 4.26/1.89  tff(c_20, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.26/1.89  tff(c_322, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.26/1.89  tff(c_950, plain, (![A_170, B_171, A_172]: (k1_relset_1(A_170, B_171, A_172)=k1_relat_1(A_172) | ~r1_tarski(A_172, k2_zfmisc_1(A_170, B_171)))), inference(resolution, [status(thm)], [c_16, c_322])).
% 4.26/1.89  tff(c_979, plain, (![A_9]: (k1_relset_1(k1_relat_1(A_9), k2_relat_1(A_9), A_9)=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_20, c_950])).
% 4.26/1.89  tff(c_450, plain, (![B_111, C_112, A_113]: (k1_xboole_0=B_111 | v1_funct_2(C_112, A_113, B_111) | k1_relset_1(A_113, B_111, C_112)!=A_113 | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_111))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.89  tff(c_1635, plain, (![B_216, A_217, A_218]: (k1_xboole_0=B_216 | v1_funct_2(A_217, A_218, B_216) | k1_relset_1(A_218, B_216, A_217)!=A_218 | ~r1_tarski(A_217, k2_zfmisc_1(A_218, B_216)))), inference(resolution, [status(thm)], [c_16, c_450])).
% 4.26/1.89  tff(c_2328, plain, (![A_251]: (k2_relat_1(A_251)=k1_xboole_0 | v1_funct_2(A_251, k1_relat_1(A_251), k2_relat_1(A_251)) | k1_relset_1(k1_relat_1(A_251), k2_relat_1(A_251), A_251)!=k1_relat_1(A_251) | ~v1_relat_1(A_251))), inference(resolution, [status(thm)], [c_20, c_1635])).
% 4.26/1.89  tff(c_54, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.26/1.89  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.26/1.89  tff(c_58, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 4.26/1.89  tff(c_95, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.26/1.89  tff(c_2335, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2328, c_95])).
% 4.26/1.89  tff(c_2353, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2335])).
% 4.26/1.89  tff(c_2356, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_2353])).
% 4.26/1.89  tff(c_2359, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_979, c_2356])).
% 4.26/1.89  tff(c_2363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2359])).
% 4.26/1.89  tff(c_2364, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2353])).
% 4.26/1.89  tff(c_174, plain, (![A_66]: (r1_tarski(A_66, k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66))) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.26/1.89  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.89  tff(c_181, plain, (![A_66]: (k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66))=A_66 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66)), A_66) | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_174, c_2])).
% 4.26/1.89  tff(c_2373, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0), '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2364, c_181])).
% 4.26/1.89  tff(c_2388, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_401, c_10, c_10, c_2364, c_2373])).
% 4.26/1.89  tff(c_40, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.89  tff(c_61, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 4.26/1.89  tff(c_310, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_61])).
% 4.26/1.89  tff(c_314, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_310])).
% 4.26/1.89  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_314])).
% 4.26/1.89  tff(c_320, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_61])).
% 4.26/1.89  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.89  tff(c_750, plain, (![B_146, C_147]: (k1_relset_1(k1_xboole_0, B_146, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_322])).
% 4.26/1.89  tff(c_752, plain, (![B_146]: (k1_relset_1(k1_xboole_0, B_146, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_320, c_750])).
% 4.26/1.89  tff(c_757, plain, (![B_146]: (k1_relset_1(k1_xboole_0, B_146, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_400, c_752])).
% 4.26/1.89  tff(c_44, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.89  tff(c_734, plain, (![C_143, B_144]: (v1_funct_2(C_143, k1_xboole_0, B_144) | k1_relset_1(k1_xboole_0, B_144, C_143)!=k1_xboole_0 | ~m1_subset_1(C_143, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 4.26/1.89  tff(c_740, plain, (![B_144]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_144) | k1_relset_1(k1_xboole_0, B_144, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_320, c_734])).
% 4.26/1.89  tff(c_760, plain, (![B_144]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_144))), inference(demodulation, [status(thm), theory('equality')], [c_757, c_740])).
% 4.26/1.89  tff(c_2425, plain, (![B_144]: (v1_funct_2('#skF_2', '#skF_2', B_144))), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2388, c_760])).
% 4.26/1.89  tff(c_2438, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2388, c_400])).
% 4.26/1.89  tff(c_2366, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_95])).
% 4.26/1.89  tff(c_2396, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2388, c_2366])).
% 4.26/1.89  tff(c_2592, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2438, c_2396])).
% 4.26/1.89  tff(c_2852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2425, c_2592])).
% 4.26/1.89  tff(c_2853, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_58])).
% 4.26/1.89  tff(c_2862, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_2855, c_2853])).
% 4.26/1.89  tff(c_2962, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2954, c_2862])).
% 4.26/1.89  tff(c_2968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2962])).
% 4.26/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.26/1.89  
% 4.26/1.89  Inference rules
% 4.26/1.89  ----------------------
% 4.26/1.89  #Ref     : 0
% 4.26/1.89  #Sup     : 600
% 4.26/1.89  #Fact    : 0
% 4.26/1.89  #Define  : 0
% 4.26/1.89  #Split   : 3
% 4.26/1.89  #Chain   : 0
% 4.26/1.89  #Close   : 0
% 4.26/1.89  
% 4.26/1.89  Ordering : KBO
% 4.26/1.89  
% 4.26/1.89  Simplification rules
% 4.26/1.89  ----------------------
% 4.26/1.89  #Subsume      : 65
% 4.26/1.89  #Demod        : 1227
% 4.26/1.89  #Tautology    : 322
% 4.26/1.89  #SimpNegUnit  : 0
% 4.26/1.89  #BackRed      : 68
% 4.26/1.89  
% 4.26/1.89  #Partial instantiations: 0
% 4.26/1.89  #Strategies tried      : 1
% 4.26/1.89  
% 4.26/1.89  Timing (in seconds)
% 4.26/1.89  ----------------------
% 4.26/1.90  Preprocessing        : 0.33
% 4.26/1.90  Parsing              : 0.16
% 4.26/1.90  CNF conversion       : 0.02
% 4.26/1.90  Main loop            : 0.67
% 4.26/1.90  Inferencing          : 0.24
% 4.26/1.90  Reduction            : 0.24
% 4.26/1.90  Demodulation         : 0.18
% 4.26/1.90  BG Simplification    : 0.03
% 4.26/1.90  Subsumption          : 0.11
% 4.26/1.90  Abstraction          : 0.04
% 4.26/1.90  MUC search           : 0.00
% 4.26/1.90  Cooper               : 0.00
% 4.26/1.90  Total                : 1.04
% 4.26/1.90  Index Insertion      : 0.00
% 4.26/1.90  Index Deletion       : 0.00
% 4.26/1.90  Index Matching       : 0.00
% 4.26/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
