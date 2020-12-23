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
% DateTime   : Thu Dec  3 10:11:11 EST 2020

% Result     : Theorem 13.81s
% Output     : CNFRefutation 13.98s
% Verified   : 
% Statistics : Number of formulae       :  383 (6770 expanded)
%              Number of leaves         :   42 (2191 expanded)
%              Depth                    :   21
%              Number of atoms          :  691 (16434 expanded)
%              Number of equality atoms :  266 (5278 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_119,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(c_32,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36576,plain,(
    ! [B_1866,A_1867] :
      ( v1_relat_1(B_1866)
      | ~ m1_subset_1(B_1866,k1_zfmisc_1(A_1867))
      | ~ v1_relat_1(A_1867) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36588,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_36576])).

tff(c_36598,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36588])).

tff(c_37086,plain,(
    ! [C_1925,A_1926,B_1927] :
      ( v4_relat_1(C_1925,A_1926)
      | ~ m1_subset_1(C_1925,k1_zfmisc_1(k2_zfmisc_1(A_1926,B_1927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_37110,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_37086])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37189,plain,(
    ! [A_1938,B_1939,C_1940] :
      ( k2_relset_1(A_1938,B_1939,C_1940) = k2_relat_1(C_1940)
      | ~ m1_subset_1(C_1940,k1_zfmisc_1(k2_zfmisc_1(A_1938,B_1939))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_37214,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_37189])).

tff(c_72,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_37254,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37214,c_72])).

tff(c_37537,plain,(
    ! [C_1963,A_1964,B_1965] :
      ( m1_subset_1(C_1963,k1_zfmisc_1(k2_zfmisc_1(A_1964,B_1965)))
      | ~ r1_tarski(k2_relat_1(C_1963),B_1965)
      | ~ r1_tarski(k1_relat_1(C_1963),A_1964)
      | ~ v1_relat_1(C_1963) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9646,plain,(
    ! [A_505,B_506,C_507] :
      ( k1_relset_1(A_505,B_506,C_507) = k1_relat_1(C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_505,B_506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_9666,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_9646])).

tff(c_10073,plain,(
    ! [B_554,A_555,C_556] :
      ( k1_xboole_0 = B_554
      | k1_relset_1(A_555,B_554,C_556) = A_555
      | ~ v1_funct_2(C_556,A_555,B_554)
      | ~ m1_subset_1(C_556,k1_zfmisc_1(k2_zfmisc_1(A_555,B_554))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10086,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_10073])).

tff(c_10099,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_9666,c_10086])).

tff(c_10100,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_10099])).

tff(c_205,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_217,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_205])).

tff(c_227,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_217])).

tff(c_9733,plain,(
    ! [A_514,B_515,C_516] :
      ( k2_relset_1(A_514,B_515,C_516) = k2_relat_1(C_516)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9753,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_9733])).

tff(c_9770,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9753,c_72])).

tff(c_9829,plain,(
    ! [C_523,A_524,B_525] :
      ( m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525)))
      | ~ r1_tarski(k2_relat_1(C_523),B_525)
      | ~ r1_tarski(k1_relat_1(C_523),A_524)
      | ~ v1_relat_1(C_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15373,plain,(
    ! [C_744,A_745,B_746] :
      ( r1_tarski(C_744,k2_zfmisc_1(A_745,B_746))
      | ~ r1_tarski(k2_relat_1(C_744),B_746)
      | ~ r1_tarski(k1_relat_1(C_744),A_745)
      | ~ v1_relat_1(C_744) ) ),
    inference(resolution,[status(thm)],[c_9829,c_20])).

tff(c_15381,plain,(
    ! [A_745] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_745,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_745)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9770,c_15373])).

tff(c_15412,plain,(
    ! [A_747] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_747,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_747) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_10100,c_15381])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9665,plain,(
    ! [A_505,B_506,A_10] :
      ( k1_relset_1(A_505,B_506,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_505,B_506)) ) ),
    inference(resolution,[status(thm)],[c_22,c_9646])).

tff(c_15417,plain,(
    ! [A_747] :
      ( k1_relset_1(A_747,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_747) ) ),
    inference(resolution,[status(thm)],[c_15412,c_9665])).

tff(c_15565,plain,(
    ! [A_751] :
      ( k1_relset_1(A_751,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10100,c_15417])).

tff(c_15580,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_15565])).

tff(c_42,plain,(
    ! [A_25] : k2_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_211,plain,(
    ! [A_38] :
      ( v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k2_zfmisc_1(A_38,A_38)) ) ),
    inference(resolution,[status(thm)],[c_54,c_205])).

tff(c_236,plain,(
    ! [A_64] : v1_relat_1(k6_relat_1(A_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_211])).

tff(c_36,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_242,plain,(
    ! [A_64] :
      ( k2_relat_1(k6_relat_1(A_64)) != k1_xboole_0
      | k6_relat_1(A_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_236,c_36])).

tff(c_264,plain,(
    ! [A_67] :
      ( k1_xboole_0 != A_67
      | k6_relat_1(A_67) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_242])).

tff(c_306,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_42])).

tff(c_18,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [A_51,B_52] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_51,B_52)),B_52) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_139,plain,(
    ! [B_9] : r1_tarski(k2_relat_1(k1_xboole_0),B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_136])).

tff(c_307,plain,(
    ! [B_9] : r1_tarski(k1_xboole_0,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_139])).

tff(c_246,plain,(
    ! [A_64] :
      ( k1_xboole_0 != A_64
      | k6_relat_1(A_64) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_242])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9258,plain,(
    ! [C_455,A_456,B_457] :
      ( v4_relat_1(C_455,A_456)
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9335,plain,(
    ! [C_466,A_467] :
      ( v4_relat_1(C_466,A_467)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_9258])).

tff(c_9346,plain,(
    ! [A_469,A_470] :
      ( v4_relat_1(A_469,A_470)
      | ~ r1_tarski(A_469,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_9335])).

tff(c_223,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_211])).

tff(c_40,plain,(
    ! [A_25] : k1_relat_1(k6_relat_1(A_25)) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9297,plain,(
    ! [B_461,A_462] :
      ( r1_tarski(k1_relat_1(B_461),A_462)
      | ~ v4_relat_1(B_461,A_462)
      | ~ v1_relat_1(B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_9313,plain,(
    ! [A_25,A_462] :
      ( r1_tarski(A_25,A_462)
      | ~ v4_relat_1(k6_relat_1(A_25),A_462)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_9297])).

tff(c_9319,plain,(
    ! [A_25,A_462] :
      ( r1_tarski(A_25,A_462)
      | ~ v4_relat_1(k6_relat_1(A_25),A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_9313])).

tff(c_9549,plain,(
    ! [A_497,A_498] :
      ( r1_tarski(A_497,A_498)
      | ~ r1_tarski(k6_relat_1(A_497),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_9346,c_9319])).

tff(c_9557,plain,(
    ! [A_64,A_498] :
      ( r1_tarski(A_64,A_498)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 != A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_9549])).

tff(c_9564,plain,(
    ! [A_499,A_500] :
      ( r1_tarski(A_499,A_500)
      | k1_xboole_0 != A_499 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_9557])).

tff(c_336,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_353,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_72,c_336])).

tff(c_9282,plain,(
    ~ r1_tarski('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_9594,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_9564,c_9282])).

tff(c_15403,plain,(
    ! [A_745] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_745,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_745) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_10100,c_15381])).

tff(c_9971,plain,(
    ! [B_541,C_542,A_543] :
      ( k1_xboole_0 = B_541
      | v1_funct_2(C_542,A_543,B_541)
      | k1_relset_1(A_543,B_541,C_542) != A_543
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_543,B_541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_16831,plain,(
    ! [B_798,A_799,A_800] :
      ( k1_xboole_0 = B_798
      | v1_funct_2(A_799,A_800,B_798)
      | k1_relset_1(A_800,B_798,A_799) != A_800
      | ~ r1_tarski(A_799,k2_zfmisc_1(A_800,B_798)) ) ),
    inference(resolution,[status(thm)],[c_22,c_9971])).

tff(c_16834,plain,(
    ! [A_745] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_745,'#skF_4')
      | k1_relset_1(A_745,'#skF_4','#skF_5') != A_745
      | ~ r1_tarski('#skF_2',A_745) ) ),
    inference(resolution,[status(thm)],[c_15403,c_16831])).

tff(c_16907,plain,(
    ! [A_801] :
      ( v1_funct_2('#skF_5',A_801,'#skF_4')
      | k1_relset_1(A_801,'#skF_4','#skF_5') != A_801
      | ~ r1_tarski('#skF_2',A_801) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9594,c_16834])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_68])).

tff(c_145,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_16916,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_16907,c_145])).

tff(c_16922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15580,c_16916])).

tff(c_16923,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_17483,plain,(
    ! [A_882,B_883,C_884] :
      ( k2_relset_1(A_882,B_883,C_884) = k2_relat_1(C_884)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_882,B_883))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_17493,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_17483])).

tff(c_17504,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16923,c_17493])).

tff(c_235,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_227,c_36])).

tff(c_288,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_17505,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17504,c_288])).

tff(c_17428,plain,(
    ! [A_872,B_873,C_874] :
      ( k1_relset_1(A_872,B_873,C_874) = k1_relat_1(C_874)
      | ~ m1_subset_1(C_874,k1_zfmisc_1(k2_zfmisc_1(A_872,B_873))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_17448,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_17428])).

tff(c_17720,plain,(
    ! [B_904,A_905,C_906] :
      ( k1_xboole_0 = B_904
      | k1_relset_1(A_905,B_904,C_906) = A_905
      | ~ v1_funct_2(C_906,A_905,B_904)
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(A_905,B_904))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_17733,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_17720])).

tff(c_17746,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_17448,c_17733])).

tff(c_17747,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_17746])).

tff(c_17522,plain,(
    ! [C_886,A_887,B_888] :
      ( m1_subset_1(C_886,k1_zfmisc_1(k2_zfmisc_1(A_887,B_888)))
      | ~ r1_tarski(k2_relat_1(C_886),B_888)
      | ~ r1_tarski(k1_relat_1(C_886),A_887)
      | ~ v1_relat_1(C_886) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_48,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26212,plain,(
    ! [A_1153,B_1154,C_1155] :
      ( k1_relset_1(A_1153,B_1154,C_1155) = k1_relat_1(C_1155)
      | ~ r1_tarski(k2_relat_1(C_1155),B_1154)
      | ~ r1_tarski(k1_relat_1(C_1155),A_1153)
      | ~ v1_relat_1(C_1155) ) ),
    inference(resolution,[status(thm)],[c_17522,c_48])).

tff(c_26220,plain,(
    ! [A_1153,B_1154] :
      ( k1_relset_1(A_1153,B_1154,'#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_4',B_1154)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_1153)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17504,c_26212])).

tff(c_26690,plain,(
    ! [A_1160,B_1161] :
      ( k1_relset_1(A_1160,B_1161,'#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_4',B_1161)
      | ~ r1_tarski('#skF_2',A_1160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_17747,c_17747,c_26220])).

tff(c_26703,plain,(
    ! [A_1162] :
      ( k1_relset_1(A_1162,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_1162) ) ),
    inference(resolution,[status(thm)],[c_8,c_26690])).

tff(c_26718,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_26703])).

tff(c_52,plain,(
    ! [C_37,A_35,B_36] :
      ( m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ r1_tarski(k2_relat_1(C_37),B_36)
      | ~ r1_tarski(k1_relat_1(C_37),A_35)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_17846,plain,(
    ! [B_912,C_913,A_914] :
      ( k1_xboole_0 = B_912
      | v1_funct_2(C_913,A_914,B_912)
      | k1_relset_1(A_914,B_912,C_913) != A_914
      | ~ m1_subset_1(C_913,k1_zfmisc_1(k2_zfmisc_1(A_914,B_912))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_27429,plain,(
    ! [B_1193,C_1194,A_1195] :
      ( k1_xboole_0 = B_1193
      | v1_funct_2(C_1194,A_1195,B_1193)
      | k1_relset_1(A_1195,B_1193,C_1194) != A_1195
      | ~ r1_tarski(k2_relat_1(C_1194),B_1193)
      | ~ r1_tarski(k1_relat_1(C_1194),A_1195)
      | ~ v1_relat_1(C_1194) ) ),
    inference(resolution,[status(thm)],[c_52,c_17846])).

tff(c_27437,plain,(
    ! [B_1193,A_1195] :
      ( k1_xboole_0 = B_1193
      | v1_funct_2('#skF_5',A_1195,B_1193)
      | k1_relset_1(A_1195,B_1193,'#skF_5') != A_1195
      | ~ r1_tarski('#skF_4',B_1193)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_1195)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17504,c_27429])).

tff(c_27568,plain,(
    ! [B_1201,A_1202] :
      ( k1_xboole_0 = B_1201
      | v1_funct_2('#skF_5',A_1202,B_1201)
      | k1_relset_1(A_1202,B_1201,'#skF_5') != A_1202
      | ~ r1_tarski('#skF_4',B_1201)
      | ~ r1_tarski('#skF_2',A_1202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_17747,c_27437])).

tff(c_27579,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_27568,c_145])).

tff(c_27588,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_26718,c_27579])).

tff(c_27590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17505,c_27588])).

tff(c_27591,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_38,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_234,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_227,c_38])).

tff(c_259,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_27594,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27591,c_259])).

tff(c_27592,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_27610,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27591,c_27592])).

tff(c_27669,plain,(
    ! [B_1207] : k2_zfmisc_1('#skF_5',B_1207) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27591,c_27591,c_18])).

tff(c_34,plain,(
    ! [A_22,B_23] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_22,B_23)),B_23) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_27685,plain,(
    ! [B_1207] : r1_tarski(k2_relat_1('#skF_5'),B_1207) ),
    inference(superposition,[status(thm),theory(equality)],[c_27669,c_34])).

tff(c_27695,plain,(
    ! [B_1207] : r1_tarski('#skF_5',B_1207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27610,c_27685])).

tff(c_166,plain,(
    ! [A_59] : m1_subset_1(k6_relat_1(A_59),k1_zfmisc_1(k2_zfmisc_1(A_59,A_59))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_178,plain,(
    ! [A_59] : r1_tarski(k6_relat_1(A_59),k2_zfmisc_1(A_59,A_59)) ),
    inference(resolution,[status(thm)],[c_166,c_20])).

tff(c_27678,plain,(
    r1_tarski(k6_relat_1('#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_27669,c_178])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27707,plain,
    ( k6_relat_1('#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k6_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_27678,c_4])).

tff(c_27710,plain,(
    k6_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27695,c_27707])).

tff(c_27724,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_27710,c_40])).

tff(c_27734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27594,c_27724])).

tff(c_27735,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_239,plain,(
    ! [A_64] :
      ( k1_relat_1(k6_relat_1(A_64)) != k1_xboole_0
      | k6_relat_1(A_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_236,c_38])).

tff(c_244,plain,(
    ! [A_64] :
      ( k1_xboole_0 != A_64
      | k6_relat_1(A_64) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_239])).

tff(c_27851,plain,(
    ! [A_1217] :
      ( A_1217 != '#skF_5'
      | k6_relat_1(A_1217) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_244])).

tff(c_27932,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_27851,c_42])).

tff(c_27742,plain,(
    ! [B_9] : r1_tarski(k2_relat_1('#skF_5'),B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_139])).

tff(c_29026,plain,(
    ! [B_9] : r1_tarski('#skF_5',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27932,c_27742])).

tff(c_27847,plain,(
    ! [A_64] :
      ( A_64 != '#skF_5'
      | k6_relat_1(A_64) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_244])).

tff(c_27746,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_16])).

tff(c_27906,plain,(
    ! [C_1219,A_1220,B_1221] :
      ( v4_relat_1(C_1219,A_1220)
      | ~ m1_subset_1(C_1219,k1_zfmisc_1(k2_zfmisc_1(A_1220,B_1221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30456,plain,(
    ! [C_1485,A_1486] :
      ( v4_relat_1(C_1485,A_1486)
      | ~ m1_subset_1(C_1485,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27746,c_27906])).

tff(c_30465,plain,(
    ! [A_1487,A_1488] :
      ( v4_relat_1(A_1487,A_1488)
      | ~ r1_tarski(A_1487,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_30456])).

tff(c_29043,plain,(
    ! [B_1332,A_1333] :
      ( r1_tarski(k1_relat_1(B_1332),A_1333)
      | ~ v4_relat_1(B_1332,A_1333)
      | ~ v1_relat_1(B_1332) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_29055,plain,(
    ! [A_25,A_1333] :
      ( r1_tarski(A_25,A_1333)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1333)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_29043])).

tff(c_29061,plain,(
    ! [A_25,A_1333] :
      ( r1_tarski(A_25,A_1333)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1333) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_29055])).

tff(c_30480,plain,(
    ! [A_1491,A_1492] :
      ( r1_tarski(A_1491,A_1492)
      | ~ r1_tarski(k6_relat_1(A_1491),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30465,c_29061])).

tff(c_30482,plain,(
    ! [A_64,A_1492] :
      ( r1_tarski(A_64,A_1492)
      | ~ r1_tarski('#skF_5','#skF_5')
      | A_64 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27847,c_30480])).

tff(c_30487,plain,(
    ! [A_1493,A_1494] :
      ( r1_tarski(A_1493,A_1494)
      | A_1493 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29026,c_30482])).

tff(c_27747,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_97])).

tff(c_27736,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_27774,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27736])).

tff(c_28322,plain,(
    ! [A_1273,B_1274,C_1275] :
      ( k1_relset_1(A_1273,B_1274,C_1275) = k1_relat_1(C_1275)
      | ~ m1_subset_1(C_1275,k1_zfmisc_1(k2_zfmisc_1(A_1273,B_1274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28338,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_28322])).

tff(c_28343,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27774,c_28338])).

tff(c_66,plain,(
    ! [B_40,A_39,C_41] :
      ( k1_xboole_0 = B_40
      | k1_relset_1(A_39,B_40,C_41) = A_39
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_28690,plain,(
    ! [B_1309,A_1310,C_1311] :
      ( B_1309 = '#skF_5'
      | k1_relset_1(A_1310,B_1309,C_1311) = A_1310
      | ~ v1_funct_2(C_1311,A_1310,B_1309)
      | ~ m1_subset_1(C_1311,k1_zfmisc_1(k2_zfmisc_1(A_1310,B_1309))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_66])).

tff(c_28709,plain,
    ( '#skF_5' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_28690])).

tff(c_28717,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28343,c_28709])).

tff(c_28718,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27747,c_28717])).

tff(c_27745,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_18])).

tff(c_28763,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28718,c_28718,c_27745])).

tff(c_27934,plain,(
    ! [B_9] : r1_tarski('#skF_5',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27932,c_27742])).

tff(c_28000,plain,(
    ! [B_1230,A_1231] :
      ( v4_relat_1(B_1230,A_1231)
      | ~ r1_tarski(k1_relat_1(B_1230),A_1231)
      | ~ v1_relat_1(B_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28006,plain,(
    ! [A_1231] :
      ( v4_relat_1('#skF_5',A_1231)
      | ~ r1_tarski('#skF_5',A_1231)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27774,c_28000])).

tff(c_28016,plain,(
    ! [A_1231] : v4_relat_1('#skF_5',A_1231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_27934,c_28006])).

tff(c_27955,plain,(
    ! [B_1226,A_1227] :
      ( r1_tarski(k1_relat_1(B_1226),A_1227)
      | ~ v4_relat_1(B_1226,A_1227)
      | ~ v1_relat_1(B_1226) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_27967,plain,(
    ! [A_25,A_1227] :
      ( r1_tarski(A_25,A_1227)
      | ~ v4_relat_1(k6_relat_1(A_25),A_1227)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_27955])).

tff(c_28067,plain,(
    ! [A_1238,A_1239] :
      ( r1_tarski(A_1238,A_1239)
      | ~ v4_relat_1(k6_relat_1(A_1238),A_1239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_27967])).

tff(c_28080,plain,(
    ! [A_64,A_1239] :
      ( r1_tarski(A_64,A_1239)
      | ~ v4_relat_1('#skF_5',A_1239)
      | A_64 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27847,c_28067])).

tff(c_28115,plain,(
    ! [A_1244,A_1245] :
      ( r1_tarski(A_1244,A_1245)
      | A_1244 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28016,c_28080])).

tff(c_147,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_155,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_147])).

tff(c_27754,plain,(
    ! [B_1209,A_1210] :
      ( B_1209 = A_1210
      | ~ r1_tarski(B_1209,A_1210)
      | ~ r1_tarski(A_1210,B_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27766,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_155,c_27754])).

tff(c_27931,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_27766])).

tff(c_28142,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_28115,c_27931])).

tff(c_28750,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28718,c_28142])).

tff(c_29003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28763,c_28750])).

tff(c_29004,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27766])).

tff(c_46,plain,(
    ! [C_28,A_26,B_27] :
      ( v4_relat_1(C_28,A_26)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_29065,plain,(
    ! [C_1335] :
      ( v4_relat_1(C_1335,'#skF_2')
      | ~ m1_subset_1(C_1335,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29004,c_46])).

tff(c_29075,plain,(
    ! [A_10] :
      ( v4_relat_1(A_10,'#skF_2')
      | ~ r1_tarski(A_10,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_29065])).

tff(c_29130,plain,(
    ! [A_1341,A_1342] :
      ( r1_tarski(A_1341,A_1342)
      | ~ v4_relat_1(k6_relat_1(A_1341),A_1342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_29055])).

tff(c_29289,plain,(
    ! [A_1359] :
      ( r1_tarski(A_1359,'#skF_2')
      | ~ r1_tarski(k6_relat_1(A_1359),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_29075,c_29130])).

tff(c_29292,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,'#skF_2')
      | ~ r1_tarski('#skF_5','#skF_5')
      | A_64 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27847,c_29289])).

tff(c_29296,plain,(
    ! [A_1360] :
      ( r1_tarski(A_1360,'#skF_2')
      | A_1360 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29292])).

tff(c_29308,plain,(
    ! [A_1360] :
      ( A_1360 = '#skF_2'
      | ~ r1_tarski('#skF_2',A_1360)
      | A_1360 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_29296,c_4])).

tff(c_30516,plain,(
    ! [A_1494] :
      ( A_1494 = '#skF_2'
      | A_1494 != '#skF_5'
      | '#skF_5' != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_30487,c_29308])).

tff(c_30612,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30516])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_31256,plain,(
    ! [B_1570,A_1571] :
      ( B_1570 = '#skF_5'
      | A_1571 = '#skF_5'
      | k2_zfmisc_1(A_1571,B_1570) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_27735,c_14])).

tff(c_31259,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_29004,c_31256])).

tff(c_31269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30612,c_27747,c_31259])).

tff(c_31271,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30516])).

tff(c_31306,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31271,c_31271,c_27774])).

tff(c_29220,plain,(
    ! [C_1351] :
      ( v4_relat_1(C_1351,'#skF_5')
      | ~ m1_subset_1(C_1351,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27745,c_27906])).

tff(c_29231,plain,(
    ! [A_1352] :
      ( v4_relat_1(A_1352,'#skF_5')
      | ~ r1_tarski(A_1352,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_29220])).

tff(c_29378,plain,(
    ! [A_1378] :
      ( r1_tarski(A_1378,'#skF_5')
      | ~ r1_tarski(k6_relat_1(A_1378),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_29231,c_29061])).

tff(c_29381,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,'#skF_5')
      | ~ r1_tarski('#skF_5','#skF_5')
      | A_64 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27847,c_29378])).

tff(c_29399,plain,(
    ! [A_1380] :
      ( r1_tarski(A_1380,'#skF_5')
      | A_1380 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29381])).

tff(c_224,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(A_10)
      | ~ v1_relat_1(B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_205])).

tff(c_29416,plain,(
    ! [A_1380] :
      ( v1_relat_1(A_1380)
      | ~ v1_relat_1('#skF_5')
      | A_1380 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_29399,c_224])).

tff(c_29439,plain,(
    ! [A_1381] :
      ( v1_relat_1(A_1381)
      | A_1381 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_29416])).

tff(c_29307,plain,(
    ! [A_1360] :
      ( v1_relat_1(A_1360)
      | ~ v1_relat_1('#skF_2')
      | A_1360 != '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_29296,c_224])).

tff(c_29309,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_29307])).

tff(c_29452,plain,(
    '#skF_5' != '#skF_2' ),
    inference(resolution,[status(thm)],[c_29439,c_29309])).

tff(c_30338,plain,(
    ! [B_1466,A_1467] :
      ( B_1466 = '#skF_5'
      | A_1467 = '#skF_5'
      | k2_zfmisc_1(A_1467,B_1466) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_27735,c_14])).

tff(c_30341,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_29004,c_30338])).

tff(c_30351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29452,c_27747,c_30341])).

tff(c_30353,plain,(
    v1_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_29307])).

tff(c_27738,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != '#skF_5'
      | A_24 = '#skF_5'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_38])).

tff(c_30361,plain,
    ( k1_relat_1('#skF_2') != '#skF_5'
    | '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30353,c_27738])).

tff(c_30413,plain,(
    k1_relat_1('#skF_2') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30361])).

tff(c_31288,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31271,c_30413])).

tff(c_31366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31306,c_31288])).

tff(c_31367,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30361])).

tff(c_27741,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != '#skF_5'
      | A_24 = '#skF_5'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27735,c_27735,c_36])).

tff(c_30360,plain,
    ( k2_relat_1('#skF_2') != '#skF_5'
    | '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30353,c_27741])).

tff(c_30402,plain,(
    k2_relat_1('#skF_2') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30360])).

tff(c_31369,plain,(
    k2_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31367,c_30402])).

tff(c_31387,plain,(
    ! [B_9] : r1_tarski('#skF_2',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31367,c_29026])).

tff(c_31590,plain,(
    ! [B_1597] : k2_zfmisc_1('#skF_2',B_1597) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31367,c_31367,c_27745])).

tff(c_31611,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31590,c_178])).

tff(c_31663,plain,
    ( k6_relat_1('#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_31611,c_4])).

tff(c_31669,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31387,c_31663])).

tff(c_31699,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_31669,c_42])).

tff(c_31712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31369,c_31699])).

tff(c_31713,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30360])).

tff(c_30352,plain,(
    ! [A_1360] :
      ( v1_relat_1(A_1360)
      | A_1360 != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_29307])).

tff(c_31717,plain,(
    ! [A_1360] :
      ( v1_relat_1(A_1360)
      | A_1360 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31713,c_30352])).

tff(c_29239,plain,(
    ! [B_1353,A_1354] :
      ( v4_relat_1(B_1353,A_1354)
      | ~ r1_tarski(k1_relat_1(B_1353),A_1354)
      | ~ v1_relat_1(B_1353) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_29245,plain,(
    ! [A_1354] :
      ( v4_relat_1('#skF_5',A_1354)
      | ~ r1_tarski('#skF_5',A_1354)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27774,c_29239])).

tff(c_29255,plain,(
    ! [A_1354] : v4_relat_1('#skF_5',A_1354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_29026,c_29245])).

tff(c_31720,plain,(
    ! [A_1354] : v4_relat_1('#skF_2',A_1354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31713,c_29255])).

tff(c_32107,plain,(
    ! [A_1626] :
      ( A_1626 != '#skF_2'
      | k6_relat_1(A_1626) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31713,c_31713,c_27847])).

tff(c_32119,plain,(
    ! [A_1626,A_1333] :
      ( r1_tarski(A_1626,A_1333)
      | ~ v4_relat_1('#skF_2',A_1333)
      | A_1626 != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32107,c_29061])).

tff(c_32143,plain,(
    ! [A_1626,A_1333] :
      ( r1_tarski(A_1626,A_1333)
      | A_1626 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31720,c_32119])).

tff(c_32710,plain,(
    ! [A_1690,A_1691,B_1692] :
      ( v4_relat_1(A_1690,A_1691)
      | ~ r1_tarski(A_1690,k2_zfmisc_1(A_1691,B_1692)) ) ),
    inference(resolution,[status(thm)],[c_22,c_27906])).

tff(c_32741,plain,(
    ! [A_1626,A_1691] :
      ( v4_relat_1(A_1626,A_1691)
      | A_1626 != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_32143,c_32710])).

tff(c_29033,plain,(
    ! [B_1331] : r1_tarski('#skF_5',B_1331) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27932,c_27742])).

tff(c_29076,plain,(
    ! [B_1336] :
      ( B_1336 = '#skF_5'
      | ~ r1_tarski(B_1336,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_29033,c_4])).

tff(c_29093,plain,(
    ! [B_19] :
      ( k1_relat_1(B_19) = '#skF_5'
      | ~ v4_relat_1(B_19,'#skF_5')
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_29076])).

tff(c_34346,plain,(
    ! [B_1788] :
      ( k1_relat_1(B_1788) = '#skF_2'
      | ~ v4_relat_1(B_1788,'#skF_2')
      | ~ v1_relat_1(B_1788) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31713,c_31713,c_29093])).

tff(c_34402,plain,(
    ! [A_1789] :
      ( k1_relat_1(A_1789) = '#skF_2'
      | ~ v1_relat_1(A_1789)
      | A_1789 != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_32741,c_34346])).

tff(c_34424,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_31717,c_34402])).

tff(c_31849,plain,(
    ! [A_1611,B_1612,C_1613] :
      ( k1_relset_1(A_1611,B_1612,C_1613) = k1_relat_1(C_1613)
      | ~ m1_subset_1(C_1613,k1_zfmisc_1(k2_zfmisc_1(A_1611,B_1612))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_33425,plain,(
    ! [A_1747,B_1748,A_1749] :
      ( k1_relset_1(A_1747,B_1748,A_1749) = k1_relat_1(A_1749)
      | ~ r1_tarski(A_1749,k2_zfmisc_1(A_1747,B_1748)) ) ),
    inference(resolution,[status(thm)],[c_22,c_31849])).

tff(c_34544,plain,(
    ! [A_1747,B_1748] : k1_relset_1(A_1747,B_1748,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32143,c_33425])).

tff(c_31743,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31713,c_27735])).

tff(c_56,plain,(
    ! [A_39] :
      ( v1_funct_2(k1_xboole_0,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_39,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_84,plain,(
    ! [A_39] :
      ( v1_funct_2(k1_xboole_0,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_31756,plain,(
    ! [A_39] :
      ( v1_funct_2('#skF_2',A_39,'#skF_2')
      | A_39 = '#skF_2'
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31743,c_31743,c_31743,c_31743,c_31743,c_84])).

tff(c_31757,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_31756])).

tff(c_31812,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_31757])).

tff(c_31816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_31812])).

tff(c_31818,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_31756])).

tff(c_60,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_82,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_32186,plain,(
    ! [C_1630,B_1631] :
      ( v1_funct_2(C_1630,'#skF_2',B_1631)
      | k1_relset_1('#skF_2',B_1631,C_1630) != '#skF_2'
      | ~ m1_subset_1(C_1630,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31743,c_31743,c_31743,c_31743,c_82])).

tff(c_32192,plain,(
    ! [B_1631] :
      ( v1_funct_2('#skF_2','#skF_2',B_1631)
      | k1_relset_1('#skF_2',B_1631,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_31818,c_32186])).

tff(c_36517,plain,(
    ! [B_1631] : v1_funct_2('#skF_2','#skF_2',B_1631) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34424,c_34544,c_32192])).

tff(c_31744,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31713,c_145])).

tff(c_36521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36517,c_31744])).

tff(c_36522,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_37560,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_37537,c_36522])).

tff(c_37578,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36598,c_37254,c_37560])).

tff(c_37587,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_37578])).

tff(c_37593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36598,c_37110,c_37587])).

tff(c_37595,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_37613,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37595,c_37595,c_16])).

tff(c_37621,plain,(
    ! [A_1968,B_1969] : v1_relat_1(k2_zfmisc_1(A_1968,B_1969)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37623,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37613,c_37621])).

tff(c_37962,plain,(
    ! [B_1996,A_1997] :
      ( v1_relat_1(B_1996)
      | ~ m1_subset_1(B_1996,k1_zfmisc_1(A_1997))
      | ~ v1_relat_1(A_1997) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37974,plain,(
    ! [A_38] :
      ( v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k2_zfmisc_1(A_38,A_38)) ) ),
    inference(resolution,[status(thm)],[c_54,c_37962])).

tff(c_37985,plain,(
    ! [A_1998] : v1_relat_1(k6_relat_1(A_1998)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_37974])).

tff(c_37717,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != '#skF_3'
      | A_24 = '#skF_3'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37595,c_37595,c_36])).

tff(c_37988,plain,(
    ! [A_1998] :
      ( k2_relat_1(k6_relat_1(A_1998)) != '#skF_3'
      | k6_relat_1(A_1998) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_37985,c_37717])).

tff(c_37993,plain,(
    ! [A_1998] :
      ( A_1998 != '#skF_3'
      | k6_relat_1(A_1998) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_37988])).

tff(c_37634,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37595,c_37595,c_18])).

tff(c_38232,plain,(
    ! [C_2026,A_2027,B_2028] :
      ( v4_relat_1(C_2026,A_2027)
      | ~ m1_subset_1(C_2026,k1_zfmisc_1(k2_zfmisc_1(A_2027,B_2028))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38249,plain,(
    ! [C_2029] :
      ( v4_relat_1(C_2029,'#skF_3')
      | ~ m1_subset_1(C_2029,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37634,c_38232])).

tff(c_38260,plain,(
    ! [A_2030] :
      ( v4_relat_1(A_2030,'#skF_3')
      | ~ r1_tarski(A_2030,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_38249])).

tff(c_37984,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_37974])).

tff(c_38086,plain,(
    ! [B_2008,A_2009] :
      ( r1_tarski(k1_relat_1(B_2008),A_2009)
      | ~ v4_relat_1(B_2008,A_2009)
      | ~ v1_relat_1(B_2008) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38098,plain,(
    ! [A_25,A_2009] :
      ( r1_tarski(A_25,A_2009)
      | ~ v4_relat_1(k6_relat_1(A_25),A_2009)
      | ~ v1_relat_1(k6_relat_1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_38086])).

tff(c_38103,plain,(
    ! [A_25,A_2009] :
      ( r1_tarski(A_25,A_2009)
      | ~ v4_relat_1(k6_relat_1(A_25),A_2009) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37984,c_38098])).

tff(c_38282,plain,(
    ! [A_2036] :
      ( r1_tarski(A_2036,'#skF_3')
      | ~ r1_tarski(k6_relat_1(A_2036),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38260,c_38103])).

tff(c_38285,plain,(
    ! [A_1998] :
      ( r1_tarski(A_1998,'#skF_3')
      | ~ r1_tarski('#skF_3','#skF_3')
      | A_1998 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37993,c_38282])).

tff(c_38289,plain,(
    ! [A_2037] :
      ( r1_tarski(A_2037,'#skF_3')
      | A_2037 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38285])).

tff(c_37978,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(A_10)
      | ~ v1_relat_1(B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_22,c_37962])).

tff(c_38295,plain,(
    ! [A_2037] :
      ( v1_relat_1(A_2037)
      | ~ v1_relat_1('#skF_3')
      | A_2037 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_38289,c_37978])).

tff(c_38311,plain,(
    ! [A_2037] :
      ( v1_relat_1(A_2037)
      | A_2037 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37623,c_38295])).

tff(c_38266,plain,(
    ! [C_2031,A_2032] :
      ( v4_relat_1(C_2031,A_2032)
      | ~ m1_subset_1(C_2031,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37613,c_38232])).

tff(c_38276,plain,(
    ! [A_2034,A_2035] :
      ( v4_relat_1(A_2034,A_2035)
      | ~ r1_tarski(A_2034,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_38266])).

tff(c_38465,plain,(
    ! [A_2060,A_2061] :
      ( r1_tarski(A_2060,A_2061)
      | ~ r1_tarski(k6_relat_1(A_2060),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38276,c_38103])).

tff(c_38473,plain,(
    ! [A_1998,A_2061] :
      ( r1_tarski(A_1998,A_2061)
      | ~ r1_tarski('#skF_3','#skF_3')
      | A_1998 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37993,c_38465])).

tff(c_38477,plain,(
    ! [A_1998,A_2061] :
      ( r1_tarski(A_1998,A_2061)
      | A_1998 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38473])).

tff(c_38755,plain,(
    ! [A_2091,A_2092,B_2093] :
      ( v4_relat_1(A_2091,A_2092)
      | ~ r1_tarski(A_2091,k2_zfmisc_1(A_2092,B_2093)) ) ),
    inference(resolution,[status(thm)],[c_22,c_38232])).

tff(c_38786,plain,(
    ! [A_1998,A_2092] :
      ( v4_relat_1(A_1998,A_2092)
      | A_1998 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_38477,c_38755])).

tff(c_38002,plain,(
    ! [A_1999] :
      ( A_1999 != '#skF_3'
      | k6_relat_1(A_1999) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_37988])).

tff(c_38066,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_38002,c_42])).

tff(c_37656,plain,(
    ! [A_1973,B_1974] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_1973,B_1974)),B_1974) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_37659,plain,(
    ! [B_9] : r1_tarski(k2_relat_1('#skF_3'),B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_37634,c_37656])).

tff(c_37728,plain,(
    ! [B_1984,A_1985] :
      ( B_1984 = A_1985
      | ~ r1_tarski(B_1984,A_1985)
      | ~ r1_tarski(A_1985,B_1984) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37746,plain,(
    ! [B_9] :
      ( k2_relat_1('#skF_3') = B_9
      | ~ r1_tarski(B_9,k2_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_37659,c_37728])).

tff(c_38104,plain,(
    ! [B_2010] :
      ( B_2010 = '#skF_3'
      | ~ r1_tarski(B_2010,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38066,c_38066,c_37746])).

tff(c_40211,plain,(
    ! [B_2178] :
      ( k1_relat_1(B_2178) = '#skF_3'
      | ~ v4_relat_1(B_2178,'#skF_3')
      | ~ v1_relat_1(B_2178) ) ),
    inference(resolution,[status(thm)],[c_30,c_38104])).

tff(c_40263,plain,(
    ! [A_2179] :
      ( k1_relat_1(A_2179) = '#skF_3'
      | ~ v1_relat_1(A_2179)
      | A_2179 != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_38786,c_40211])).

tff(c_40285,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38311,c_40263])).

tff(c_37774,plain,(
    ! [B_1987,A_1988] :
      ( v1_relat_1(B_1987)
      | ~ m1_subset_1(B_1987,k1_zfmisc_1(A_1988))
      | ~ v1_relat_1(A_1988) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37783,plain,(
    ! [A_38] :
      ( v1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k2_zfmisc_1(A_38,A_38)) ) ),
    inference(resolution,[status(thm)],[c_54,c_37774])).

tff(c_37805,plain,(
    ! [A_1989] : v1_relat_1(k6_relat_1(A_1989)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_37783])).

tff(c_37677,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != '#skF_3'
      | A_24 = '#skF_3'
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37595,c_37595,c_38])).

tff(c_37811,plain,(
    ! [A_1989] :
      ( k1_relat_1(k6_relat_1(A_1989)) != '#skF_3'
      | k6_relat_1(A_1989) = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_37805,c_37677])).

tff(c_37819,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_37811])).

tff(c_37663,plain,(
    ! [A_1975] : m1_subset_1(k6_relat_1(A_1975),k1_zfmisc_1(k2_zfmisc_1(A_1975,A_1975))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_37667,plain,(
    m1_subset_1(k6_relat_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37634,c_37663])).

tff(c_37688,plain,(
    ! [A_1978,B_1979] :
      ( r1_tarski(A_1978,B_1979)
      | ~ m1_subset_1(A_1978,k1_zfmisc_1(B_1979)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37698,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_37667,c_37688])).

tff(c_37744,plain,
    ( k6_relat_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37698,c_37728])).

tff(c_37773,plain,(
    ~ r1_tarski('#skF_3',k6_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_37744])).

tff(c_37820,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37819,c_37773])).

tff(c_37825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_37820])).

tff(c_37826,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_37744])).

tff(c_37889,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_37826,c_42])).

tff(c_37901,plain,(
    ! [B_9] : r1_tarski('#skF_3',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37889,c_37659])).

tff(c_37594,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_37601,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37595,c_37594])).

tff(c_37655,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37613,c_37601,c_74])).

tff(c_37700,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_37655,c_37688])).

tff(c_37745,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_37700,c_37728])).

tff(c_37754,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_37745])).

tff(c_37908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37901,c_37754])).

tff(c_37909,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_37745])).

tff(c_37925,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37909,c_37655])).

tff(c_38358,plain,(
    ! [A_2045,B_2046,C_2047] :
      ( k1_relset_1(A_2045,B_2046,C_2047) = k1_relat_1(C_2047)
      | ~ m1_subset_1(C_2047,k1_zfmisc_1(k2_zfmisc_1(A_2045,B_2046))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40330,plain,(
    ! [B_2183,C_2184] :
      ( k1_relset_1('#skF_3',B_2183,C_2184) = k1_relat_1(C_2184)
      | ~ m1_subset_1(C_2184,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37634,c_38358])).

tff(c_40334,plain,(
    ! [B_2183] : k1_relset_1('#skF_3',B_2183,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_37925,c_40330])).

tff(c_40341,plain,(
    ! [B_2183] : k1_relset_1('#skF_3',B_2183,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40285,c_40334])).

tff(c_38802,plain,(
    ! [C_2096,B_2097] :
      ( v1_funct_2(C_2096,'#skF_3',B_2097)
      | k1_relset_1('#skF_3',B_2097,C_2096) != '#skF_3'
      | ~ m1_subset_1(C_2096,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37595,c_37595,c_37595,c_37595,c_82])).

tff(c_38828,plain,(
    ! [B_2105] :
      ( v1_funct_2('#skF_3','#skF_3',B_2105)
      | k1_relset_1('#skF_3',B_2105,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_37925,c_38802])).

tff(c_37675,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37601,c_37655,c_37634,c_37601,c_80])).

tff(c_37924,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37909,c_37675])).

tff(c_38844,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_38828,c_37924])).

tff(c_40347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40341,c_38844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.81/5.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.98/5.85  
% 13.98/5.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.98/5.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 13.98/5.86  
% 13.98/5.86  %Foreground sorts:
% 13.98/5.86  
% 13.98/5.86  
% 13.98/5.86  %Background operators:
% 13.98/5.86  
% 13.98/5.86  
% 13.98/5.86  %Foreground operators:
% 13.98/5.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.98/5.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.98/5.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.98/5.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.98/5.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.98/5.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.98/5.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.98/5.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.98/5.86  tff('#skF_5', type, '#skF_5': $i).
% 13.98/5.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.98/5.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.98/5.86  tff('#skF_2', type, '#skF_2': $i).
% 13.98/5.86  tff('#skF_3', type, '#skF_3': $i).
% 13.98/5.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.98/5.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.98/5.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.98/5.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.98/5.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.98/5.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.98/5.86  tff('#skF_4', type, '#skF_4': $i).
% 13.98/5.86  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.98/5.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.98/5.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.98/5.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.98/5.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.98/5.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.98/5.86  
% 13.98/5.90  tff(f_81, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.98/5.90  tff(f_157, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 13.98/5.90  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.98/5.90  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.98/5.90  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 13.98/5.90  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.98/5.90  tff(f_117, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 13.98/5.90  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.98/5.90  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.98/5.90  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.98/5.90  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.98/5.90  tff(f_95, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.98/5.90  tff(f_119, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 13.98/5.90  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 13.98/5.90  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.98/5.90  tff(f_83, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 13.98/5.90  tff(c_32, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.98/5.90  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.98/5.90  tff(c_36576, plain, (![B_1866, A_1867]: (v1_relat_1(B_1866) | ~m1_subset_1(B_1866, k1_zfmisc_1(A_1867)) | ~v1_relat_1(A_1867))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.98/5.90  tff(c_36588, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_36576])).
% 13.98/5.90  tff(c_36598, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36588])).
% 13.98/5.90  tff(c_37086, plain, (![C_1925, A_1926, B_1927]: (v4_relat_1(C_1925, A_1926) | ~m1_subset_1(C_1925, k1_zfmisc_1(k2_zfmisc_1(A_1926, B_1927))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.98/5.90  tff(c_37110, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_37086])).
% 13.98/5.90  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_37189, plain, (![A_1938, B_1939, C_1940]: (k2_relset_1(A_1938, B_1939, C_1940)=k2_relat_1(C_1940) | ~m1_subset_1(C_1940, k1_zfmisc_1(k2_zfmisc_1(A_1938, B_1939))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.98/5.90  tff(c_37214, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_37189])).
% 13.98/5.90  tff(c_72, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.98/5.90  tff(c_37254, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37214, c_72])).
% 13.98/5.90  tff(c_37537, plain, (![C_1963, A_1964, B_1965]: (m1_subset_1(C_1963, k1_zfmisc_1(k2_zfmisc_1(A_1964, B_1965))) | ~r1_tarski(k2_relat_1(C_1963), B_1965) | ~r1_tarski(k1_relat_1(C_1963), A_1964) | ~v1_relat_1(C_1963))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.98/5.90  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.98/5.90  tff(c_70, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.98/5.90  tff(c_97, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_70])).
% 13.98/5.90  tff(c_76, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.98/5.90  tff(c_9646, plain, (![A_505, B_506, C_507]: (k1_relset_1(A_505, B_506, C_507)=k1_relat_1(C_507) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_505, B_506))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.98/5.90  tff(c_9666, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_9646])).
% 13.98/5.90  tff(c_10073, plain, (![B_554, A_555, C_556]: (k1_xboole_0=B_554 | k1_relset_1(A_555, B_554, C_556)=A_555 | ~v1_funct_2(C_556, A_555, B_554) | ~m1_subset_1(C_556, k1_zfmisc_1(k2_zfmisc_1(A_555, B_554))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_10086, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_10073])).
% 13.98/5.90  tff(c_10099, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_9666, c_10086])).
% 13.98/5.90  tff(c_10100, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_97, c_10099])).
% 13.98/5.90  tff(c_205, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.98/5.90  tff(c_217, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_205])).
% 13.98/5.90  tff(c_227, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_217])).
% 13.98/5.90  tff(c_9733, plain, (![A_514, B_515, C_516]: (k2_relset_1(A_514, B_515, C_516)=k2_relat_1(C_516) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.98/5.90  tff(c_9753, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_9733])).
% 13.98/5.90  tff(c_9770, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9753, c_72])).
% 13.98/5.90  tff(c_9829, plain, (![C_523, A_524, B_525]: (m1_subset_1(C_523, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))) | ~r1_tarski(k2_relat_1(C_523), B_525) | ~r1_tarski(k1_relat_1(C_523), A_524) | ~v1_relat_1(C_523))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.98/5.90  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.98/5.90  tff(c_15373, plain, (![C_744, A_745, B_746]: (r1_tarski(C_744, k2_zfmisc_1(A_745, B_746)) | ~r1_tarski(k2_relat_1(C_744), B_746) | ~r1_tarski(k1_relat_1(C_744), A_745) | ~v1_relat_1(C_744))), inference(resolution, [status(thm)], [c_9829, c_20])).
% 13.98/5.90  tff(c_15381, plain, (![A_745]: (r1_tarski('#skF_5', k2_zfmisc_1(A_745, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_745) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_9770, c_15373])).
% 13.98/5.90  tff(c_15412, plain, (![A_747]: (r1_tarski('#skF_5', k2_zfmisc_1(A_747, '#skF_4')) | ~r1_tarski('#skF_2', A_747))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_10100, c_15381])).
% 13.98/5.90  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.98/5.90  tff(c_9665, plain, (![A_505, B_506, A_10]: (k1_relset_1(A_505, B_506, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_505, B_506)))), inference(resolution, [status(thm)], [c_22, c_9646])).
% 13.98/5.90  tff(c_15417, plain, (![A_747]: (k1_relset_1(A_747, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_747))), inference(resolution, [status(thm)], [c_15412, c_9665])).
% 13.98/5.90  tff(c_15565, plain, (![A_751]: (k1_relset_1(A_751, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_751))), inference(demodulation, [status(thm), theory('equality')], [c_10100, c_15417])).
% 13.98/5.90  tff(c_15580, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_15565])).
% 13.98/5.90  tff(c_42, plain, (![A_25]: (k2_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.98/5.90  tff(c_54, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.98/5.90  tff(c_211, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k2_zfmisc_1(A_38, A_38)))), inference(resolution, [status(thm)], [c_54, c_205])).
% 13.98/5.90  tff(c_236, plain, (![A_64]: (v1_relat_1(k6_relat_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_211])).
% 13.98/5.90  tff(c_36, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.98/5.90  tff(c_242, plain, (![A_64]: (k2_relat_1(k6_relat_1(A_64))!=k1_xboole_0 | k6_relat_1(A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_236, c_36])).
% 13.98/5.90  tff(c_264, plain, (![A_67]: (k1_xboole_0!=A_67 | k6_relat_1(A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_242])).
% 13.98/5.90  tff(c_306, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_264, c_42])).
% 13.98/5.90  tff(c_18, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.98/5.90  tff(c_136, plain, (![A_51, B_52]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_51, B_52)), B_52))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.98/5.90  tff(c_139, plain, (![B_9]: (r1_tarski(k2_relat_1(k1_xboole_0), B_9))), inference(superposition, [status(thm), theory('equality')], [c_18, c_136])).
% 13.98/5.90  tff(c_307, plain, (![B_9]: (r1_tarski(k1_xboole_0, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_139])).
% 13.98/5.90  tff(c_246, plain, (![A_64]: (k1_xboole_0!=A_64 | k6_relat_1(A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_242])).
% 13.98/5.90  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.98/5.90  tff(c_9258, plain, (![C_455, A_456, B_457]: (v4_relat_1(C_455, A_456) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.98/5.90  tff(c_9335, plain, (![C_466, A_467]: (v4_relat_1(C_466, A_467) | ~m1_subset_1(C_466, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_9258])).
% 13.98/5.90  tff(c_9346, plain, (![A_469, A_470]: (v4_relat_1(A_469, A_470) | ~r1_tarski(A_469, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_9335])).
% 13.98/5.90  tff(c_223, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_211])).
% 13.98/5.90  tff(c_40, plain, (![A_25]: (k1_relat_1(k6_relat_1(A_25))=A_25)), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.98/5.90  tff(c_9297, plain, (![B_461, A_462]: (r1_tarski(k1_relat_1(B_461), A_462) | ~v4_relat_1(B_461, A_462) | ~v1_relat_1(B_461))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_9313, plain, (![A_25, A_462]: (r1_tarski(A_25, A_462) | ~v4_relat_1(k6_relat_1(A_25), A_462) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_9297])).
% 13.98/5.90  tff(c_9319, plain, (![A_25, A_462]: (r1_tarski(A_25, A_462) | ~v4_relat_1(k6_relat_1(A_25), A_462))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_9313])).
% 13.98/5.90  tff(c_9549, plain, (![A_497, A_498]: (r1_tarski(A_497, A_498) | ~r1_tarski(k6_relat_1(A_497), k1_xboole_0))), inference(resolution, [status(thm)], [c_9346, c_9319])).
% 13.98/5.90  tff(c_9557, plain, (![A_64, A_498]: (r1_tarski(A_64, A_498) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_xboole_0!=A_64)), inference(superposition, [status(thm), theory('equality')], [c_246, c_9549])).
% 13.98/5.90  tff(c_9564, plain, (![A_499, A_500]: (r1_tarski(A_499, A_500) | k1_xboole_0!=A_499)), inference(demodulation, [status(thm), theory('equality')], [c_307, c_9557])).
% 13.98/5.90  tff(c_336, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.98/5.90  tff(c_353, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_72, c_336])).
% 13.98/5.90  tff(c_9282, plain, (~r1_tarski('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_353])).
% 13.98/5.90  tff(c_9594, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_9564, c_9282])).
% 13.98/5.90  tff(c_15403, plain, (![A_745]: (r1_tarski('#skF_5', k2_zfmisc_1(A_745, '#skF_4')) | ~r1_tarski('#skF_2', A_745))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_10100, c_15381])).
% 13.98/5.90  tff(c_9971, plain, (![B_541, C_542, A_543]: (k1_xboole_0=B_541 | v1_funct_2(C_542, A_543, B_541) | k1_relset_1(A_543, B_541, C_542)!=A_543 | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_543, B_541))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_16831, plain, (![B_798, A_799, A_800]: (k1_xboole_0=B_798 | v1_funct_2(A_799, A_800, B_798) | k1_relset_1(A_800, B_798, A_799)!=A_800 | ~r1_tarski(A_799, k2_zfmisc_1(A_800, B_798)))), inference(resolution, [status(thm)], [c_22, c_9971])).
% 13.98/5.90  tff(c_16834, plain, (![A_745]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_745, '#skF_4') | k1_relset_1(A_745, '#skF_4', '#skF_5')!=A_745 | ~r1_tarski('#skF_2', A_745))), inference(resolution, [status(thm)], [c_15403, c_16831])).
% 13.98/5.90  tff(c_16907, plain, (![A_801]: (v1_funct_2('#skF_5', A_801, '#skF_4') | k1_relset_1(A_801, '#skF_4', '#skF_5')!=A_801 | ~r1_tarski('#skF_2', A_801))), inference(negUnitSimplification, [status(thm)], [c_9594, c_16834])).
% 13.98/5.90  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.98/5.90  tff(c_68, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 13.98/5.90  tff(c_80, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_68])).
% 13.98/5.90  tff(c_145, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_80])).
% 13.98/5.90  tff(c_16916, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_16907, c_145])).
% 13.98/5.90  tff(c_16922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_15580, c_16916])).
% 13.98/5.90  tff(c_16923, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_353])).
% 13.98/5.90  tff(c_17483, plain, (![A_882, B_883, C_884]: (k2_relset_1(A_882, B_883, C_884)=k2_relat_1(C_884) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_882, B_883))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.98/5.90  tff(c_17493, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_17483])).
% 13.98/5.90  tff(c_17504, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16923, c_17493])).
% 13.98/5.90  tff(c_235, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_227, c_36])).
% 13.98/5.90  tff(c_288, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_235])).
% 13.98/5.90  tff(c_17505, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17504, c_288])).
% 13.98/5.90  tff(c_17428, plain, (![A_872, B_873, C_874]: (k1_relset_1(A_872, B_873, C_874)=k1_relat_1(C_874) | ~m1_subset_1(C_874, k1_zfmisc_1(k2_zfmisc_1(A_872, B_873))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.98/5.90  tff(c_17448, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_17428])).
% 13.98/5.90  tff(c_17720, plain, (![B_904, A_905, C_906]: (k1_xboole_0=B_904 | k1_relset_1(A_905, B_904, C_906)=A_905 | ~v1_funct_2(C_906, A_905, B_904) | ~m1_subset_1(C_906, k1_zfmisc_1(k2_zfmisc_1(A_905, B_904))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_17733, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_17720])).
% 13.98/5.90  tff(c_17746, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_17448, c_17733])).
% 13.98/5.90  tff(c_17747, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_97, c_17746])).
% 13.98/5.90  tff(c_17522, plain, (![C_886, A_887, B_888]: (m1_subset_1(C_886, k1_zfmisc_1(k2_zfmisc_1(A_887, B_888))) | ~r1_tarski(k2_relat_1(C_886), B_888) | ~r1_tarski(k1_relat_1(C_886), A_887) | ~v1_relat_1(C_886))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.98/5.90  tff(c_48, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.98/5.90  tff(c_26212, plain, (![A_1153, B_1154, C_1155]: (k1_relset_1(A_1153, B_1154, C_1155)=k1_relat_1(C_1155) | ~r1_tarski(k2_relat_1(C_1155), B_1154) | ~r1_tarski(k1_relat_1(C_1155), A_1153) | ~v1_relat_1(C_1155))), inference(resolution, [status(thm)], [c_17522, c_48])).
% 13.98/5.90  tff(c_26220, plain, (![A_1153, B_1154]: (k1_relset_1(A_1153, B_1154, '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_4', B_1154) | ~r1_tarski(k1_relat_1('#skF_5'), A_1153) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17504, c_26212])).
% 13.98/5.90  tff(c_26690, plain, (![A_1160, B_1161]: (k1_relset_1(A_1160, B_1161, '#skF_5')='#skF_2' | ~r1_tarski('#skF_4', B_1161) | ~r1_tarski('#skF_2', A_1160))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_17747, c_17747, c_26220])).
% 13.98/5.90  tff(c_26703, plain, (![A_1162]: (k1_relset_1(A_1162, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_1162))), inference(resolution, [status(thm)], [c_8, c_26690])).
% 13.98/5.90  tff(c_26718, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_8, c_26703])).
% 13.98/5.90  tff(c_52, plain, (![C_37, A_35, B_36]: (m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~r1_tarski(k2_relat_1(C_37), B_36) | ~r1_tarski(k1_relat_1(C_37), A_35) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_117])).
% 13.98/5.90  tff(c_17846, plain, (![B_912, C_913, A_914]: (k1_xboole_0=B_912 | v1_funct_2(C_913, A_914, B_912) | k1_relset_1(A_914, B_912, C_913)!=A_914 | ~m1_subset_1(C_913, k1_zfmisc_1(k2_zfmisc_1(A_914, B_912))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_27429, plain, (![B_1193, C_1194, A_1195]: (k1_xboole_0=B_1193 | v1_funct_2(C_1194, A_1195, B_1193) | k1_relset_1(A_1195, B_1193, C_1194)!=A_1195 | ~r1_tarski(k2_relat_1(C_1194), B_1193) | ~r1_tarski(k1_relat_1(C_1194), A_1195) | ~v1_relat_1(C_1194))), inference(resolution, [status(thm)], [c_52, c_17846])).
% 13.98/5.90  tff(c_27437, plain, (![B_1193, A_1195]: (k1_xboole_0=B_1193 | v1_funct_2('#skF_5', A_1195, B_1193) | k1_relset_1(A_1195, B_1193, '#skF_5')!=A_1195 | ~r1_tarski('#skF_4', B_1193) | ~r1_tarski(k1_relat_1('#skF_5'), A_1195) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17504, c_27429])).
% 13.98/5.90  tff(c_27568, plain, (![B_1201, A_1202]: (k1_xboole_0=B_1201 | v1_funct_2('#skF_5', A_1202, B_1201) | k1_relset_1(A_1202, B_1201, '#skF_5')!=A_1202 | ~r1_tarski('#skF_4', B_1201) | ~r1_tarski('#skF_2', A_1202))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_17747, c_27437])).
% 13.98/5.90  tff(c_27579, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_27568, c_145])).
% 13.98/5.90  tff(c_27588, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_26718, c_27579])).
% 13.98/5.90  tff(c_27590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17505, c_27588])).
% 13.98/5.90  tff(c_27591, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_235])).
% 13.98/5.90  tff(c_38, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.98/5.90  tff(c_234, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_227, c_38])).
% 13.98/5.90  tff(c_259, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_234])).
% 13.98/5.90  tff(c_27594, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27591, c_259])).
% 13.98/5.90  tff(c_27592, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_235])).
% 13.98/5.90  tff(c_27610, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27591, c_27592])).
% 13.98/5.90  tff(c_27669, plain, (![B_1207]: (k2_zfmisc_1('#skF_5', B_1207)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27591, c_27591, c_18])).
% 13.98/5.90  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_22, B_23)), B_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.98/5.90  tff(c_27685, plain, (![B_1207]: (r1_tarski(k2_relat_1('#skF_5'), B_1207))), inference(superposition, [status(thm), theory('equality')], [c_27669, c_34])).
% 13.98/5.90  tff(c_27695, plain, (![B_1207]: (r1_tarski('#skF_5', B_1207))), inference(demodulation, [status(thm), theory('equality')], [c_27610, c_27685])).
% 13.98/5.90  tff(c_166, plain, (![A_59]: (m1_subset_1(k6_relat_1(A_59), k1_zfmisc_1(k2_zfmisc_1(A_59, A_59))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.98/5.90  tff(c_178, plain, (![A_59]: (r1_tarski(k6_relat_1(A_59), k2_zfmisc_1(A_59, A_59)))), inference(resolution, [status(thm)], [c_166, c_20])).
% 13.98/5.90  tff(c_27678, plain, (r1_tarski(k6_relat_1('#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27669, c_178])).
% 13.98/5.90  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.98/5.90  tff(c_27707, plain, (k6_relat_1('#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k6_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_27678, c_4])).
% 13.98/5.90  tff(c_27710, plain, (k6_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27695, c_27707])).
% 13.98/5.90  tff(c_27724, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_27710, c_40])).
% 13.98/5.90  tff(c_27734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27594, c_27724])).
% 13.98/5.90  tff(c_27735, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_234])).
% 13.98/5.90  tff(c_239, plain, (![A_64]: (k1_relat_1(k6_relat_1(A_64))!=k1_xboole_0 | k6_relat_1(A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_236, c_38])).
% 13.98/5.90  tff(c_244, plain, (![A_64]: (k1_xboole_0!=A_64 | k6_relat_1(A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_239])).
% 13.98/5.90  tff(c_27851, plain, (![A_1217]: (A_1217!='#skF_5' | k6_relat_1(A_1217)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_244])).
% 13.98/5.90  tff(c_27932, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_27851, c_42])).
% 13.98/5.90  tff(c_27742, plain, (![B_9]: (r1_tarski(k2_relat_1('#skF_5'), B_9))), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_139])).
% 13.98/5.90  tff(c_29026, plain, (![B_9]: (r1_tarski('#skF_5', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_27932, c_27742])).
% 13.98/5.90  tff(c_27847, plain, (![A_64]: (A_64!='#skF_5' | k6_relat_1(A_64)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_244])).
% 13.98/5.90  tff(c_27746, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_16])).
% 13.98/5.90  tff(c_27906, plain, (![C_1219, A_1220, B_1221]: (v4_relat_1(C_1219, A_1220) | ~m1_subset_1(C_1219, k1_zfmisc_1(k2_zfmisc_1(A_1220, B_1221))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.98/5.90  tff(c_30456, plain, (![C_1485, A_1486]: (v4_relat_1(C_1485, A_1486) | ~m1_subset_1(C_1485, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_27746, c_27906])).
% 13.98/5.90  tff(c_30465, plain, (![A_1487, A_1488]: (v4_relat_1(A_1487, A_1488) | ~r1_tarski(A_1487, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_30456])).
% 13.98/5.90  tff(c_29043, plain, (![B_1332, A_1333]: (r1_tarski(k1_relat_1(B_1332), A_1333) | ~v4_relat_1(B_1332, A_1333) | ~v1_relat_1(B_1332))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_29055, plain, (![A_25, A_1333]: (r1_tarski(A_25, A_1333) | ~v4_relat_1(k6_relat_1(A_25), A_1333) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_29043])).
% 13.98/5.90  tff(c_29061, plain, (![A_25, A_1333]: (r1_tarski(A_25, A_1333) | ~v4_relat_1(k6_relat_1(A_25), A_1333))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_29055])).
% 13.98/5.90  tff(c_30480, plain, (![A_1491, A_1492]: (r1_tarski(A_1491, A_1492) | ~r1_tarski(k6_relat_1(A_1491), '#skF_5'))), inference(resolution, [status(thm)], [c_30465, c_29061])).
% 13.98/5.90  tff(c_30482, plain, (![A_64, A_1492]: (r1_tarski(A_64, A_1492) | ~r1_tarski('#skF_5', '#skF_5') | A_64!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27847, c_30480])).
% 13.98/5.90  tff(c_30487, plain, (![A_1493, A_1494]: (r1_tarski(A_1493, A_1494) | A_1493!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_29026, c_30482])).
% 13.98/5.90  tff(c_27747, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_97])).
% 13.98/5.90  tff(c_27736, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_234])).
% 13.98/5.90  tff(c_27774, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27736])).
% 13.98/5.90  tff(c_28322, plain, (![A_1273, B_1274, C_1275]: (k1_relset_1(A_1273, B_1274, C_1275)=k1_relat_1(C_1275) | ~m1_subset_1(C_1275, k1_zfmisc_1(k2_zfmisc_1(A_1273, B_1274))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.98/5.90  tff(c_28338, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_28322])).
% 13.98/5.90  tff(c_28343, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_27774, c_28338])).
% 13.98/5.90  tff(c_66, plain, (![B_40, A_39, C_41]: (k1_xboole_0=B_40 | k1_relset_1(A_39, B_40, C_41)=A_39 | ~v1_funct_2(C_41, A_39, B_40) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_28690, plain, (![B_1309, A_1310, C_1311]: (B_1309='#skF_5' | k1_relset_1(A_1310, B_1309, C_1311)=A_1310 | ~v1_funct_2(C_1311, A_1310, B_1309) | ~m1_subset_1(C_1311, k1_zfmisc_1(k2_zfmisc_1(A_1310, B_1309))))), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_66])).
% 13.98/5.90  tff(c_28709, plain, ('#skF_5'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_28690])).
% 13.98/5.90  tff(c_28717, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28343, c_28709])).
% 13.98/5.90  tff(c_28718, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27747, c_28717])).
% 13.98/5.90  tff(c_27745, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_18])).
% 13.98/5.90  tff(c_28763, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28718, c_28718, c_27745])).
% 13.98/5.90  tff(c_27934, plain, (![B_9]: (r1_tarski('#skF_5', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_27932, c_27742])).
% 13.98/5.90  tff(c_28000, plain, (![B_1230, A_1231]: (v4_relat_1(B_1230, A_1231) | ~r1_tarski(k1_relat_1(B_1230), A_1231) | ~v1_relat_1(B_1230))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_28006, plain, (![A_1231]: (v4_relat_1('#skF_5', A_1231) | ~r1_tarski('#skF_5', A_1231) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_27774, c_28000])).
% 13.98/5.90  tff(c_28016, plain, (![A_1231]: (v4_relat_1('#skF_5', A_1231))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_27934, c_28006])).
% 13.98/5.90  tff(c_27955, plain, (![B_1226, A_1227]: (r1_tarski(k1_relat_1(B_1226), A_1227) | ~v4_relat_1(B_1226, A_1227) | ~v1_relat_1(B_1226))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_27967, plain, (![A_25, A_1227]: (r1_tarski(A_25, A_1227) | ~v4_relat_1(k6_relat_1(A_25), A_1227) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_27955])).
% 13.98/5.90  tff(c_28067, plain, (![A_1238, A_1239]: (r1_tarski(A_1238, A_1239) | ~v4_relat_1(k6_relat_1(A_1238), A_1239))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_27967])).
% 13.98/5.90  tff(c_28080, plain, (![A_64, A_1239]: (r1_tarski(A_64, A_1239) | ~v4_relat_1('#skF_5', A_1239) | A_64!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27847, c_28067])).
% 13.98/5.90  tff(c_28115, plain, (![A_1244, A_1245]: (r1_tarski(A_1244, A_1245) | A_1244!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28016, c_28080])).
% 13.98/5.90  tff(c_147, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.98/5.90  tff(c_155, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_147])).
% 13.98/5.90  tff(c_27754, plain, (![B_1209, A_1210]: (B_1209=A_1210 | ~r1_tarski(B_1209, A_1210) | ~r1_tarski(A_1210, B_1209))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.98/5.90  tff(c_27766, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_155, c_27754])).
% 13.98/5.90  tff(c_27931, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_27766])).
% 13.98/5.90  tff(c_28142, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_5'), inference(resolution, [status(thm)], [c_28115, c_27931])).
% 13.98/5.90  tff(c_28750, plain, (k2_zfmisc_1('#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28718, c_28142])).
% 13.98/5.90  tff(c_29003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28763, c_28750])).
% 13.98/5.90  tff(c_29004, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_27766])).
% 13.98/5.90  tff(c_46, plain, (![C_28, A_26, B_27]: (v4_relat_1(C_28, A_26) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.98/5.90  tff(c_29065, plain, (![C_1335]: (v4_relat_1(C_1335, '#skF_2') | ~m1_subset_1(C_1335, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_29004, c_46])).
% 13.98/5.90  tff(c_29075, plain, (![A_10]: (v4_relat_1(A_10, '#skF_2') | ~r1_tarski(A_10, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_29065])).
% 13.98/5.90  tff(c_29130, plain, (![A_1341, A_1342]: (r1_tarski(A_1341, A_1342) | ~v4_relat_1(k6_relat_1(A_1341), A_1342))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_29055])).
% 13.98/5.90  tff(c_29289, plain, (![A_1359]: (r1_tarski(A_1359, '#skF_2') | ~r1_tarski(k6_relat_1(A_1359), '#skF_5'))), inference(resolution, [status(thm)], [c_29075, c_29130])).
% 13.98/5.90  tff(c_29292, plain, (![A_64]: (r1_tarski(A_64, '#skF_2') | ~r1_tarski('#skF_5', '#skF_5') | A_64!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27847, c_29289])).
% 13.98/5.90  tff(c_29296, plain, (![A_1360]: (r1_tarski(A_1360, '#skF_2') | A_1360!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_29292])).
% 13.98/5.90  tff(c_29308, plain, (![A_1360]: (A_1360='#skF_2' | ~r1_tarski('#skF_2', A_1360) | A_1360!='#skF_5')), inference(resolution, [status(thm)], [c_29296, c_4])).
% 13.98/5.90  tff(c_30516, plain, (![A_1494]: (A_1494='#skF_2' | A_1494!='#skF_5' | '#skF_5'!='#skF_2')), inference(resolution, [status(thm)], [c_30487, c_29308])).
% 13.98/5.90  tff(c_30612, plain, ('#skF_5'!='#skF_2'), inference(splitLeft, [status(thm)], [c_30516])).
% 13.98/5.90  tff(c_14, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.98/5.90  tff(c_31256, plain, (![B_1570, A_1571]: (B_1570='#skF_5' | A_1571='#skF_5' | k2_zfmisc_1(A_1571, B_1570)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_27735, c_14])).
% 13.98/5.90  tff(c_31259, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_29004, c_31256])).
% 13.98/5.90  tff(c_31269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30612, c_27747, c_31259])).
% 13.98/5.90  tff(c_31271, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_30516])).
% 13.98/5.90  tff(c_31306, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31271, c_31271, c_27774])).
% 13.98/5.90  tff(c_29220, plain, (![C_1351]: (v4_relat_1(C_1351, '#skF_5') | ~m1_subset_1(C_1351, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_27745, c_27906])).
% 13.98/5.90  tff(c_29231, plain, (![A_1352]: (v4_relat_1(A_1352, '#skF_5') | ~r1_tarski(A_1352, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_29220])).
% 13.98/5.90  tff(c_29378, plain, (![A_1378]: (r1_tarski(A_1378, '#skF_5') | ~r1_tarski(k6_relat_1(A_1378), '#skF_5'))), inference(resolution, [status(thm)], [c_29231, c_29061])).
% 13.98/5.90  tff(c_29381, plain, (![A_64]: (r1_tarski(A_64, '#skF_5') | ~r1_tarski('#skF_5', '#skF_5') | A_64!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27847, c_29378])).
% 13.98/5.90  tff(c_29399, plain, (![A_1380]: (r1_tarski(A_1380, '#skF_5') | A_1380!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_29381])).
% 13.98/5.90  tff(c_224, plain, (![A_10, B_11]: (v1_relat_1(A_10) | ~v1_relat_1(B_11) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_22, c_205])).
% 13.98/5.90  tff(c_29416, plain, (![A_1380]: (v1_relat_1(A_1380) | ~v1_relat_1('#skF_5') | A_1380!='#skF_5')), inference(resolution, [status(thm)], [c_29399, c_224])).
% 13.98/5.90  tff(c_29439, plain, (![A_1381]: (v1_relat_1(A_1381) | A_1381!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_29416])).
% 13.98/5.90  tff(c_29307, plain, (![A_1360]: (v1_relat_1(A_1360) | ~v1_relat_1('#skF_2') | A_1360!='#skF_5')), inference(resolution, [status(thm)], [c_29296, c_224])).
% 13.98/5.90  tff(c_29309, plain, (~v1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_29307])).
% 13.98/5.90  tff(c_29452, plain, ('#skF_5'!='#skF_2'), inference(resolution, [status(thm)], [c_29439, c_29309])).
% 13.98/5.90  tff(c_30338, plain, (![B_1466, A_1467]: (B_1466='#skF_5' | A_1467='#skF_5' | k2_zfmisc_1(A_1467, B_1466)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_27735, c_14])).
% 13.98/5.90  tff(c_30341, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_29004, c_30338])).
% 13.98/5.90  tff(c_30351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29452, c_27747, c_30341])).
% 13.98/5.90  tff(c_30353, plain, (v1_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_29307])).
% 13.98/5.90  tff(c_27738, plain, (![A_24]: (k1_relat_1(A_24)!='#skF_5' | A_24='#skF_5' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_38])).
% 13.98/5.90  tff(c_30361, plain, (k1_relat_1('#skF_2')!='#skF_5' | '#skF_5'='#skF_2'), inference(resolution, [status(thm)], [c_30353, c_27738])).
% 13.98/5.90  tff(c_30413, plain, (k1_relat_1('#skF_2')!='#skF_5'), inference(splitLeft, [status(thm)], [c_30361])).
% 13.98/5.90  tff(c_31288, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31271, c_30413])).
% 13.98/5.90  tff(c_31366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31306, c_31288])).
% 13.98/5.90  tff(c_31367, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_30361])).
% 13.98/5.90  tff(c_27741, plain, (![A_24]: (k2_relat_1(A_24)!='#skF_5' | A_24='#skF_5' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_27735, c_27735, c_36])).
% 13.98/5.90  tff(c_30360, plain, (k2_relat_1('#skF_2')!='#skF_5' | '#skF_5'='#skF_2'), inference(resolution, [status(thm)], [c_30353, c_27741])).
% 13.98/5.90  tff(c_30402, plain, (k2_relat_1('#skF_2')!='#skF_5'), inference(splitLeft, [status(thm)], [c_30360])).
% 13.98/5.90  tff(c_31369, plain, (k2_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31367, c_30402])).
% 13.98/5.90  tff(c_31387, plain, (![B_9]: (r1_tarski('#skF_2', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_31367, c_29026])).
% 13.98/5.90  tff(c_31590, plain, (![B_1597]: (k2_zfmisc_1('#skF_2', B_1597)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31367, c_31367, c_27745])).
% 13.98/5.90  tff(c_31611, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31590, c_178])).
% 13.98/5.90  tff(c_31663, plain, (k6_relat_1('#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_31611, c_4])).
% 13.98/5.90  tff(c_31669, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31387, c_31663])).
% 13.98/5.90  tff(c_31699, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_31669, c_42])).
% 13.98/5.90  tff(c_31712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31369, c_31699])).
% 13.98/5.90  tff(c_31713, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_30360])).
% 13.98/5.90  tff(c_30352, plain, (![A_1360]: (v1_relat_1(A_1360) | A_1360!='#skF_5')), inference(splitRight, [status(thm)], [c_29307])).
% 13.98/5.90  tff(c_31717, plain, (![A_1360]: (v1_relat_1(A_1360) | A_1360!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31713, c_30352])).
% 13.98/5.90  tff(c_29239, plain, (![B_1353, A_1354]: (v4_relat_1(B_1353, A_1354) | ~r1_tarski(k1_relat_1(B_1353), A_1354) | ~v1_relat_1(B_1353))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_29245, plain, (![A_1354]: (v4_relat_1('#skF_5', A_1354) | ~r1_tarski('#skF_5', A_1354) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_27774, c_29239])).
% 13.98/5.90  tff(c_29255, plain, (![A_1354]: (v4_relat_1('#skF_5', A_1354))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_29026, c_29245])).
% 13.98/5.90  tff(c_31720, plain, (![A_1354]: (v4_relat_1('#skF_2', A_1354))), inference(demodulation, [status(thm), theory('equality')], [c_31713, c_29255])).
% 13.98/5.90  tff(c_32107, plain, (![A_1626]: (A_1626!='#skF_2' | k6_relat_1(A_1626)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31713, c_31713, c_27847])).
% 13.98/5.90  tff(c_32119, plain, (![A_1626, A_1333]: (r1_tarski(A_1626, A_1333) | ~v4_relat_1('#skF_2', A_1333) | A_1626!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32107, c_29061])).
% 13.98/5.90  tff(c_32143, plain, (![A_1626, A_1333]: (r1_tarski(A_1626, A_1333) | A_1626!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31720, c_32119])).
% 13.98/5.90  tff(c_32710, plain, (![A_1690, A_1691, B_1692]: (v4_relat_1(A_1690, A_1691) | ~r1_tarski(A_1690, k2_zfmisc_1(A_1691, B_1692)))), inference(resolution, [status(thm)], [c_22, c_27906])).
% 13.98/5.90  tff(c_32741, plain, (![A_1626, A_1691]: (v4_relat_1(A_1626, A_1691) | A_1626!='#skF_2')), inference(resolution, [status(thm)], [c_32143, c_32710])).
% 13.98/5.90  tff(c_29033, plain, (![B_1331]: (r1_tarski('#skF_5', B_1331))), inference(demodulation, [status(thm), theory('equality')], [c_27932, c_27742])).
% 13.98/5.90  tff(c_29076, plain, (![B_1336]: (B_1336='#skF_5' | ~r1_tarski(B_1336, '#skF_5'))), inference(resolution, [status(thm)], [c_29033, c_4])).
% 13.98/5.90  tff(c_29093, plain, (![B_19]: (k1_relat_1(B_19)='#skF_5' | ~v4_relat_1(B_19, '#skF_5') | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_30, c_29076])).
% 13.98/5.90  tff(c_34346, plain, (![B_1788]: (k1_relat_1(B_1788)='#skF_2' | ~v4_relat_1(B_1788, '#skF_2') | ~v1_relat_1(B_1788))), inference(demodulation, [status(thm), theory('equality')], [c_31713, c_31713, c_29093])).
% 13.98/5.90  tff(c_34402, plain, (![A_1789]: (k1_relat_1(A_1789)='#skF_2' | ~v1_relat_1(A_1789) | A_1789!='#skF_2')), inference(resolution, [status(thm)], [c_32741, c_34346])).
% 13.98/5.90  tff(c_34424, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_31717, c_34402])).
% 13.98/5.90  tff(c_31849, plain, (![A_1611, B_1612, C_1613]: (k1_relset_1(A_1611, B_1612, C_1613)=k1_relat_1(C_1613) | ~m1_subset_1(C_1613, k1_zfmisc_1(k2_zfmisc_1(A_1611, B_1612))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.98/5.90  tff(c_33425, plain, (![A_1747, B_1748, A_1749]: (k1_relset_1(A_1747, B_1748, A_1749)=k1_relat_1(A_1749) | ~r1_tarski(A_1749, k2_zfmisc_1(A_1747, B_1748)))), inference(resolution, [status(thm)], [c_22, c_31849])).
% 13.98/5.90  tff(c_34544, plain, (![A_1747, B_1748]: (k1_relset_1(A_1747, B_1748, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_32143, c_33425])).
% 13.98/5.90  tff(c_31743, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_31713, c_27735])).
% 13.98/5.90  tff(c_56, plain, (![A_39]: (v1_funct_2(k1_xboole_0, A_39, k1_xboole_0) | k1_xboole_0=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_39, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_84, plain, (![A_39]: (v1_funct_2(k1_xboole_0, A_39, k1_xboole_0) | k1_xboole_0=A_39 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 13.98/5.90  tff(c_31756, plain, (![A_39]: (v1_funct_2('#skF_2', A_39, '#skF_2') | A_39='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_31743, c_31743, c_31743, c_31743, c_31743, c_84])).
% 13.98/5.90  tff(c_31757, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_31756])).
% 13.98/5.90  tff(c_31812, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_31757])).
% 13.98/5.90  tff(c_31816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_31812])).
% 13.98/5.90  tff(c_31818, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_31756])).
% 13.98/5.90  tff(c_60, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.98/5.90  tff(c_82, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_60])).
% 13.98/5.90  tff(c_32186, plain, (![C_1630, B_1631]: (v1_funct_2(C_1630, '#skF_2', B_1631) | k1_relset_1('#skF_2', B_1631, C_1630)!='#skF_2' | ~m1_subset_1(C_1630, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_31743, c_31743, c_31743, c_31743, c_82])).
% 13.98/5.90  tff(c_32192, plain, (![B_1631]: (v1_funct_2('#skF_2', '#skF_2', B_1631) | k1_relset_1('#skF_2', B_1631, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_31818, c_32186])).
% 13.98/5.90  tff(c_36517, plain, (![B_1631]: (v1_funct_2('#skF_2', '#skF_2', B_1631))), inference(demodulation, [status(thm), theory('equality')], [c_34424, c_34544, c_32192])).
% 13.98/5.90  tff(c_31744, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31713, c_145])).
% 13.98/5.90  tff(c_36521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36517, c_31744])).
% 13.98/5.90  tff(c_36522, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_80])).
% 13.98/5.90  tff(c_37560, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_37537, c_36522])).
% 13.98/5.90  tff(c_37578, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36598, c_37254, c_37560])).
% 13.98/5.90  tff(c_37587, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_37578])).
% 13.98/5.90  tff(c_37593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36598, c_37110, c_37587])).
% 13.98/5.90  tff(c_37595, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_70])).
% 13.98/5.90  tff(c_37613, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37595, c_37595, c_16])).
% 13.98/5.90  tff(c_37621, plain, (![A_1968, B_1969]: (v1_relat_1(k2_zfmisc_1(A_1968, B_1969)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.98/5.90  tff(c_37623, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37613, c_37621])).
% 13.98/5.90  tff(c_37962, plain, (![B_1996, A_1997]: (v1_relat_1(B_1996) | ~m1_subset_1(B_1996, k1_zfmisc_1(A_1997)) | ~v1_relat_1(A_1997))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.98/5.90  tff(c_37974, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k2_zfmisc_1(A_38, A_38)))), inference(resolution, [status(thm)], [c_54, c_37962])).
% 13.98/5.90  tff(c_37985, plain, (![A_1998]: (v1_relat_1(k6_relat_1(A_1998)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_37974])).
% 13.98/5.90  tff(c_37717, plain, (![A_24]: (k2_relat_1(A_24)!='#skF_3' | A_24='#skF_3' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_37595, c_37595, c_36])).
% 13.98/5.90  tff(c_37988, plain, (![A_1998]: (k2_relat_1(k6_relat_1(A_1998))!='#skF_3' | k6_relat_1(A_1998)='#skF_3')), inference(resolution, [status(thm)], [c_37985, c_37717])).
% 13.98/5.90  tff(c_37993, plain, (![A_1998]: (A_1998!='#skF_3' | k6_relat_1(A_1998)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_37988])).
% 13.98/5.90  tff(c_37634, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37595, c_37595, c_18])).
% 13.98/5.90  tff(c_38232, plain, (![C_2026, A_2027, B_2028]: (v4_relat_1(C_2026, A_2027) | ~m1_subset_1(C_2026, k1_zfmisc_1(k2_zfmisc_1(A_2027, B_2028))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.98/5.90  tff(c_38249, plain, (![C_2029]: (v4_relat_1(C_2029, '#skF_3') | ~m1_subset_1(C_2029, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_37634, c_38232])).
% 13.98/5.90  tff(c_38260, plain, (![A_2030]: (v4_relat_1(A_2030, '#skF_3') | ~r1_tarski(A_2030, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_38249])).
% 13.98/5.90  tff(c_37984, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_37974])).
% 13.98/5.90  tff(c_38086, plain, (![B_2008, A_2009]: (r1_tarski(k1_relat_1(B_2008), A_2009) | ~v4_relat_1(B_2008, A_2009) | ~v1_relat_1(B_2008))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.98/5.90  tff(c_38098, plain, (![A_25, A_2009]: (r1_tarski(A_25, A_2009) | ~v4_relat_1(k6_relat_1(A_25), A_2009) | ~v1_relat_1(k6_relat_1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_38086])).
% 13.98/5.90  tff(c_38103, plain, (![A_25, A_2009]: (r1_tarski(A_25, A_2009) | ~v4_relat_1(k6_relat_1(A_25), A_2009))), inference(demodulation, [status(thm), theory('equality')], [c_37984, c_38098])).
% 13.98/5.90  tff(c_38282, plain, (![A_2036]: (r1_tarski(A_2036, '#skF_3') | ~r1_tarski(k6_relat_1(A_2036), '#skF_3'))), inference(resolution, [status(thm)], [c_38260, c_38103])).
% 13.98/5.90  tff(c_38285, plain, (![A_1998]: (r1_tarski(A_1998, '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | A_1998!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37993, c_38282])).
% 13.98/5.90  tff(c_38289, plain, (![A_2037]: (r1_tarski(A_2037, '#skF_3') | A_2037!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38285])).
% 13.98/5.90  tff(c_37978, plain, (![A_10, B_11]: (v1_relat_1(A_10) | ~v1_relat_1(B_11) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_22, c_37962])).
% 13.98/5.90  tff(c_38295, plain, (![A_2037]: (v1_relat_1(A_2037) | ~v1_relat_1('#skF_3') | A_2037!='#skF_3')), inference(resolution, [status(thm)], [c_38289, c_37978])).
% 13.98/5.90  tff(c_38311, plain, (![A_2037]: (v1_relat_1(A_2037) | A_2037!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37623, c_38295])).
% 13.98/5.90  tff(c_38266, plain, (![C_2031, A_2032]: (v4_relat_1(C_2031, A_2032) | ~m1_subset_1(C_2031, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_37613, c_38232])).
% 13.98/5.90  tff(c_38276, plain, (![A_2034, A_2035]: (v4_relat_1(A_2034, A_2035) | ~r1_tarski(A_2034, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_38266])).
% 13.98/5.90  tff(c_38465, plain, (![A_2060, A_2061]: (r1_tarski(A_2060, A_2061) | ~r1_tarski(k6_relat_1(A_2060), '#skF_3'))), inference(resolution, [status(thm)], [c_38276, c_38103])).
% 13.98/5.90  tff(c_38473, plain, (![A_1998, A_2061]: (r1_tarski(A_1998, A_2061) | ~r1_tarski('#skF_3', '#skF_3') | A_1998!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37993, c_38465])).
% 13.98/5.90  tff(c_38477, plain, (![A_1998, A_2061]: (r1_tarski(A_1998, A_2061) | A_1998!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_38473])).
% 13.98/5.90  tff(c_38755, plain, (![A_2091, A_2092, B_2093]: (v4_relat_1(A_2091, A_2092) | ~r1_tarski(A_2091, k2_zfmisc_1(A_2092, B_2093)))), inference(resolution, [status(thm)], [c_22, c_38232])).
% 13.98/5.90  tff(c_38786, plain, (![A_1998, A_2092]: (v4_relat_1(A_1998, A_2092) | A_1998!='#skF_3')), inference(resolution, [status(thm)], [c_38477, c_38755])).
% 13.98/5.90  tff(c_38002, plain, (![A_1999]: (A_1999!='#skF_3' | k6_relat_1(A_1999)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_37988])).
% 13.98/5.90  tff(c_38066, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_38002, c_42])).
% 13.98/5.90  tff(c_37656, plain, (![A_1973, B_1974]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_1973, B_1974)), B_1974))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.98/5.90  tff(c_37659, plain, (![B_9]: (r1_tarski(k2_relat_1('#skF_3'), B_9))), inference(superposition, [status(thm), theory('equality')], [c_37634, c_37656])).
% 13.98/5.90  tff(c_37728, plain, (![B_1984, A_1985]: (B_1984=A_1985 | ~r1_tarski(B_1984, A_1985) | ~r1_tarski(A_1985, B_1984))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.98/5.90  tff(c_37746, plain, (![B_9]: (k2_relat_1('#skF_3')=B_9 | ~r1_tarski(B_9, k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_37659, c_37728])).
% 13.98/5.90  tff(c_38104, plain, (![B_2010]: (B_2010='#skF_3' | ~r1_tarski(B_2010, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38066, c_38066, c_37746])).
% 13.98/5.90  tff(c_40211, plain, (![B_2178]: (k1_relat_1(B_2178)='#skF_3' | ~v4_relat_1(B_2178, '#skF_3') | ~v1_relat_1(B_2178))), inference(resolution, [status(thm)], [c_30, c_38104])).
% 13.98/5.90  tff(c_40263, plain, (![A_2179]: (k1_relat_1(A_2179)='#skF_3' | ~v1_relat_1(A_2179) | A_2179!='#skF_3')), inference(resolution, [status(thm)], [c_38786, c_40211])).
% 13.98/5.90  tff(c_40285, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_38311, c_40263])).
% 13.98/5.90  tff(c_37774, plain, (![B_1987, A_1988]: (v1_relat_1(B_1987) | ~m1_subset_1(B_1987, k1_zfmisc_1(A_1988)) | ~v1_relat_1(A_1988))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.98/5.90  tff(c_37783, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k2_zfmisc_1(A_38, A_38)))), inference(resolution, [status(thm)], [c_54, c_37774])).
% 13.98/5.90  tff(c_37805, plain, (![A_1989]: (v1_relat_1(k6_relat_1(A_1989)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_37783])).
% 13.98/5.90  tff(c_37677, plain, (![A_24]: (k1_relat_1(A_24)!='#skF_3' | A_24='#skF_3' | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_37595, c_37595, c_38])).
% 13.98/5.90  tff(c_37811, plain, (![A_1989]: (k1_relat_1(k6_relat_1(A_1989))!='#skF_3' | k6_relat_1(A_1989)='#skF_3')), inference(resolution, [status(thm)], [c_37805, c_37677])).
% 13.98/5.90  tff(c_37819, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_37811])).
% 13.98/5.90  tff(c_37663, plain, (![A_1975]: (m1_subset_1(k6_relat_1(A_1975), k1_zfmisc_1(k2_zfmisc_1(A_1975, A_1975))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.98/5.90  tff(c_37667, plain, (m1_subset_1(k6_relat_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37634, c_37663])).
% 13.98/5.90  tff(c_37688, plain, (![A_1978, B_1979]: (r1_tarski(A_1978, B_1979) | ~m1_subset_1(A_1978, k1_zfmisc_1(B_1979)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.98/5.90  tff(c_37698, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_37667, c_37688])).
% 13.98/5.90  tff(c_37744, plain, (k6_relat_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_37698, c_37728])).
% 13.98/5.90  tff(c_37773, plain, (~r1_tarski('#skF_3', k6_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_37744])).
% 13.98/5.90  tff(c_37820, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37819, c_37773])).
% 13.98/5.90  tff(c_37825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_37820])).
% 13.98/5.90  tff(c_37826, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_37744])).
% 13.98/5.90  tff(c_37889, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_37826, c_42])).
% 13.98/5.90  tff(c_37901, plain, (![B_9]: (r1_tarski('#skF_3', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_37889, c_37659])).
% 13.98/5.90  tff(c_37594, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 13.98/5.90  tff(c_37601, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37595, c_37594])).
% 13.98/5.90  tff(c_37655, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_37613, c_37601, c_74])).
% 13.98/5.90  tff(c_37700, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_37655, c_37688])).
% 13.98/5.90  tff(c_37745, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_37700, c_37728])).
% 13.98/5.90  tff(c_37754, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_37745])).
% 13.98/5.90  tff(c_37908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37901, c_37754])).
% 13.98/5.90  tff(c_37909, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_37745])).
% 13.98/5.90  tff(c_37925, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_37909, c_37655])).
% 13.98/5.90  tff(c_38358, plain, (![A_2045, B_2046, C_2047]: (k1_relset_1(A_2045, B_2046, C_2047)=k1_relat_1(C_2047) | ~m1_subset_1(C_2047, k1_zfmisc_1(k2_zfmisc_1(A_2045, B_2046))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.98/5.90  tff(c_40330, plain, (![B_2183, C_2184]: (k1_relset_1('#skF_3', B_2183, C_2184)=k1_relat_1(C_2184) | ~m1_subset_1(C_2184, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_37634, c_38358])).
% 13.98/5.90  tff(c_40334, plain, (![B_2183]: (k1_relset_1('#skF_3', B_2183, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_37925, c_40330])).
% 13.98/5.90  tff(c_40341, plain, (![B_2183]: (k1_relset_1('#skF_3', B_2183, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40285, c_40334])).
% 13.98/5.90  tff(c_38802, plain, (![C_2096, B_2097]: (v1_funct_2(C_2096, '#skF_3', B_2097) | k1_relset_1('#skF_3', B_2097, C_2096)!='#skF_3' | ~m1_subset_1(C_2096, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_37595, c_37595, c_37595, c_37595, c_82])).
% 13.98/5.90  tff(c_38828, plain, (![B_2105]: (v1_funct_2('#skF_3', '#skF_3', B_2105) | k1_relset_1('#skF_3', B_2105, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_37925, c_38802])).
% 13.98/5.90  tff(c_37675, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37601, c_37655, c_37634, c_37601, c_80])).
% 13.98/5.90  tff(c_37924, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37909, c_37675])).
% 13.98/5.90  tff(c_38844, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_38828, c_37924])).
% 13.98/5.90  tff(c_40347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40341, c_38844])).
% 13.98/5.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.98/5.90  
% 13.98/5.90  Inference rules
% 13.98/5.90  ----------------------
% 13.98/5.90  #Ref     : 37
% 13.98/5.90  #Sup     : 9437
% 13.98/5.90  #Fact    : 0
% 13.98/5.90  #Define  : 0
% 13.98/5.90  #Split   : 76
% 13.98/5.90  #Chain   : 0
% 13.98/5.90  #Close   : 0
% 13.98/5.90  
% 13.98/5.90  Ordering : KBO
% 13.98/5.90  
% 13.98/5.90  Simplification rules
% 13.98/5.90  ----------------------
% 13.98/5.90  #Subsume      : 3884
% 13.98/5.90  #Demod        : 5892
% 13.98/5.90  #Tautology    : 3288
% 13.98/5.90  #SimpNegUnit  : 131
% 13.98/5.90  #BackRed      : 376
% 13.98/5.90  
% 13.98/5.90  #Partial instantiations: 0
% 13.98/5.90  #Strategies tried      : 1
% 13.98/5.90  
% 13.98/5.90  Timing (in seconds)
% 13.98/5.90  ----------------------
% 14.44/5.90  Preprocessing        : 0.37
% 14.44/5.90  Parsing              : 0.20
% 14.44/5.90  CNF conversion       : 0.02
% 14.44/5.90  Main loop            : 4.67
% 14.44/5.90  Inferencing          : 1.16
% 14.44/5.90  Reduction            : 1.89
% 14.44/5.91  Demodulation         : 1.38
% 14.44/5.91  BG Simplification    : 0.10
% 14.44/5.91  Subsumption          : 1.24
% 14.44/5.91  Abstraction          : 0.15
% 14.44/5.91  MUC search           : 0.00
% 14.44/5.91  Cooper               : 0.00
% 14.44/5.91  Total                : 5.15
% 14.44/5.91  Index Insertion      : 0.00
% 14.44/5.91  Index Deletion       : 0.00
% 14.44/5.91  Index Matching       : 0.00
% 14.44/5.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
