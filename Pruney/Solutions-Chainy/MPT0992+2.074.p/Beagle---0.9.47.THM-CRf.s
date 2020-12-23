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
% DateTime   : Thu Dec  3 10:13:42 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  167 (1893 expanded)
%              Number of leaves         :   36 ( 603 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 (5982 expanded)
%              Number of equality atoms :   79 (2332 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4874,plain,(
    ! [B_476,A_477] :
      ( v1_relat_1(B_476)
      | ~ m1_subset_1(B_476,k1_zfmisc_1(A_477))
      | ~ v1_relat_1(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4880,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_4874])).

tff(c_4887,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4880])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5200,plain,(
    ! [A_516,B_517,C_518] :
      ( k1_relset_1(A_516,B_517,C_518) = k1_relat_1(C_518)
      | ~ m1_subset_1(C_518,k1_zfmisc_1(k2_zfmisc_1(A_516,B_517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5223,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5200])).

tff(c_5926,plain,(
    ! [B_597,A_598,C_599] :
      ( k1_xboole_0 = B_597
      | k1_relset_1(A_598,B_597,C_599) = A_598
      | ~ v1_funct_2(C_599,A_598,B_597)
      | ~ m1_subset_1(C_599,k1_zfmisc_1(k2_zfmisc_1(A_598,B_597))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5942,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_5926])).

tff(c_5958,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5223,c_5942])).

tff(c_5959,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_5958])).

tff(c_32,plain,(
    ! [B_23,A_22] :
      ( k1_relat_1(k7_relat_1(B_23,A_22)) = A_22
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5978,plain,(
    ! [A_22] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_22)) = A_22
      | ~ r1_tarski(A_22,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5959,c_32])).

tff(c_5984,plain,(
    ! [A_22] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_22)) = A_22
      | ~ r1_tarski(A_22,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4887,c_5978])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5699,plain,(
    ! [A_580,B_581,C_582,D_583] :
      ( k2_partfun1(A_580,B_581,C_582,D_583) = k7_relat_1(C_582,D_583)
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(A_580,B_581)))
      | ~ v1_funct_1(C_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5708,plain,(
    ! [D_583] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_583) = k7_relat_1('#skF_4',D_583)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_5699])).

tff(c_5720,plain,(
    ! [D_583] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_583) = k7_relat_1('#skF_4',D_583) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5708])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_865,plain,(
    ! [B_140,A_141] :
      ( v1_relat_1(B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_141))
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_871,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_865])).

tff(c_878,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_871])).

tff(c_1166,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1185,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1166])).

tff(c_1954,plain,(
    ! [B_278,A_279,C_280] :
      ( k1_xboole_0 = B_278
      | k1_relset_1(A_279,B_278,C_280) = A_279
      | ~ v1_funct_2(C_280,A_279,B_278)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_279,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1967,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1954])).

tff(c_1981,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1185,c_1967])).

tff(c_1982,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_1981])).

tff(c_2009,plain,(
    ! [A_22] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_22)) = A_22
      | ~ r1_tarski(A_22,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1982,c_32])).

tff(c_2015,plain,(
    ! [A_22] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_22)) = A_22
      | ~ r1_tarski(A_22,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_2009])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k7_relat_1(B_21,A_20),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_133,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_133])).

tff(c_924,plain,(
    ! [A_148,C_149,B_150] :
      ( r1_tarski(A_148,C_149)
      | ~ r1_tarski(B_150,C_149)
      | ~ r1_tarski(A_148,B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_935,plain,(
    ! [A_148] :
      ( r1_tarski(A_148,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_148,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_144,c_924])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1689,plain,(
    ! [D_258,B_259,C_260,A_261] :
      ( m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(B_259,C_260)))
      | ~ r1_tarski(k1_relat_1(D_258),B_259)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_261,C_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2899,plain,(
    ! [A_355,B_356,C_357,A_358] :
      ( m1_subset_1(A_355,k1_zfmisc_1(k2_zfmisc_1(B_356,C_357)))
      | ~ r1_tarski(k1_relat_1(A_355),B_356)
      | ~ r1_tarski(A_355,k2_zfmisc_1(A_358,C_357)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1689])).

tff(c_4641,plain,(
    ! [A_464,B_465] :
      ( m1_subset_1(A_464,k1_zfmisc_1(k2_zfmisc_1(B_465,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(A_464),B_465)
      | ~ r1_tarski(A_464,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_935,c_2899])).

tff(c_1595,plain,(
    ! [A_238,B_239,C_240,D_241] :
      ( k2_partfun1(A_238,B_239,C_240,D_241) = k7_relat_1(C_240,D_241)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1602,plain,(
    ! [D_241] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_241) = k7_relat_1('#skF_4',D_241)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1595])).

tff(c_1611,plain,(
    ! [D_241] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_241) = k7_relat_1('#skF_4',D_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1602])).

tff(c_821,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( v1_funct_1(k2_partfun1(A_134,B_135,C_136,D_137))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_828,plain,(
    ! [D_137] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_137))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_821])).

tff(c_837,plain,(
    ! [D_137] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_137)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_828])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_153,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_153])).

tff(c_842,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_844,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_1616,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_844])).

tff(c_4682,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4641,c_1616])).

tff(c_4741,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4682])).

tff(c_4744,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_4741])).

tff(c_4748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_4744])).

tff(c_4749,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4682])).

tff(c_4848,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2015,c_4749])).

tff(c_4851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6,c_4848])).

tff(c_4853,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_5221,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4853,c_5200])).

tff(c_5727,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5720,c_5720,c_5221])).

tff(c_4852,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_5735,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5720,c_4852])).

tff(c_5734,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5720,c_4853])).

tff(c_6131,plain,(
    ! [B_603,C_604,A_605] :
      ( k1_xboole_0 = B_603
      | v1_funct_2(C_604,A_605,B_603)
      | k1_relset_1(A_605,B_603,C_604) != A_605
      | ~ m1_subset_1(C_604,k1_zfmisc_1(k2_zfmisc_1(A_605,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6137,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5734,c_6131])).

tff(c_6160,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5735,c_75,c_6137])).

tff(c_6380,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5727,c_6160])).

tff(c_6387,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5984,c_6380])).

tff(c_6391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6387])).

tff(c_6392,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6406,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_6392,c_16])).

tff(c_6393,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6398,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_6393])).

tff(c_6416,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6406,c_6398,c_62])).

tff(c_6872,plain,(
    ! [A_687,B_688] :
      ( r1_tarski(A_687,B_688)
      | ~ m1_subset_1(A_687,k1_zfmisc_1(B_688)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6883,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6416,c_6872])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6436,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_6392,c_10])).

tff(c_6888,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6883,c_6436])).

tff(c_6399,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6398,c_64])).

tff(c_6896,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_6888,c_6399])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6404,plain,(
    ! [A_9] : m1_subset_1('#skF_1',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_18])).

tff(c_6884,plain,(
    ! [A_9] : r1_tarski('#skF_1',A_9) ),
    inference(resolution,[status(thm)],[c_6404,c_6872])).

tff(c_6934,plain,(
    ! [A_9] : r1_tarski('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_6884])).

tff(c_6407,plain,(
    ! [B_624] : k2_zfmisc_1('#skF_1',B_624) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_6392,c_16])).

tff(c_6411,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6407,c_28])).

tff(c_6456,plain,(
    ! [B_628,A_629] :
      ( r1_tarski(k7_relat_1(B_628,A_629),B_628)
      | ~ v1_relat_1(B_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6460,plain,(
    ! [A_629] :
      ( k7_relat_1('#skF_1',A_629) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6456,c_6436])).

tff(c_6463,plain,(
    ! [A_629] : k7_relat_1('#skF_1',A_629) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6411,c_6460])).

tff(c_6891,plain,(
    ! [A_629] : k7_relat_1('#skF_4',A_629) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_6888,c_6463])).

tff(c_6900,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_6404])).

tff(c_7467,plain,(
    ! [A_782,B_783,C_784,D_785] :
      ( k2_partfun1(A_782,B_783,C_784,D_785) = k7_relat_1(C_784,D_785)
      | ~ m1_subset_1(C_784,k1_zfmisc_1(k2_zfmisc_1(A_782,B_783)))
      | ~ v1_funct_1(C_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7470,plain,(
    ! [A_782,B_783,D_785] :
      ( k2_partfun1(A_782,B_783,'#skF_4',D_785) = k7_relat_1('#skF_4',D_785)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6900,c_7467])).

tff(c_7480,plain,(
    ! [A_782,B_783,D_785] : k2_partfun1(A_782,B_783,'#skF_4',D_785) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6891,c_7470])).

tff(c_6479,plain,(
    ! [A_633,B_634] :
      ( r1_tarski(A_633,B_634)
      | ~ m1_subset_1(A_633,k1_zfmisc_1(B_634)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6490,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_6416,c_6479])).

tff(c_6495,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6490,c_6436])).

tff(c_6507,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6495,c_6404])).

tff(c_6852,plain,(
    ! [A_683,B_684,C_685,D_686] :
      ( v1_funct_1(k2_partfun1(A_683,B_684,C_685,D_686))
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_683,B_684)))
      | ~ v1_funct_1(C_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6855,plain,(
    ! [A_683,B_684,D_686] :
      ( v1_funct_1(k2_partfun1(A_683,B_684,'#skF_4',D_686))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6507,c_6852])).

tff(c_6865,plain,(
    ! [A_683,B_684,D_686] : v1_funct_1(k2_partfun1(A_683,B_684,'#skF_4',D_686)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6855])).

tff(c_6437,plain,(
    ! [A_626] :
      ( A_626 = '#skF_1'
      | ~ r1_tarski(A_626,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_6392,c_10])).

tff(c_6447,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_6437])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6417,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6392,c_6392,c_14])).

tff(c_6477,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6447,c_6398,c_6447,c_6447,c_6398,c_6398,c_6447,c_6417,c_6398,c_6398,c_56])).

tff(c_6478,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6477])).

tff(c_6497,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6495,c_6495,c_6495,c_6478])).

tff(c_6869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6865,c_6497])).

tff(c_6870,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6477])).

tff(c_7020,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_6888,c_6888,c_6888,c_6888,c_6888,c_6888,c_6888,c_6888,c_6870])).

tff(c_7021,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7020])).

tff(c_7086,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_7021])).

tff(c_7483,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7480,c_7086])).

tff(c_7488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7483])).

tff(c_7490,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7020])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7534,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_7490,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7536,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7534,c_2])).

tff(c_7545,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6934,c_7536])).

tff(c_7489,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_7020])).

tff(c_7553,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7545,c_7489])).

tff(c_7560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6896,c_7553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.46  
% 6.93/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.46  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.93/2.46  
% 6.93/2.46  %Foreground sorts:
% 6.93/2.46  
% 6.93/2.46  
% 6.93/2.46  %Background operators:
% 6.93/2.46  
% 6.93/2.46  
% 6.93/2.46  %Foreground operators:
% 6.93/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.93/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.93/2.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.93/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.93/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.93/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.93/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.93/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.93/2.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.93/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.93/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.93/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.93/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.46  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.93/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.93/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.93/2.46  
% 7.18/2.49  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 7.18/2.49  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.18/2.49  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.18/2.49  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.18/2.49  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.18/2.49  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.18/2.49  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.18/2.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.18/2.49  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 7.18/2.49  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.18/2.49  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.18/2.49  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 7.18/2.49  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.18/2.49  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.18/2.49  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.18/2.49  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.18/2.49  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.18/2.49  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.18/2.49  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.18/2.49  tff(c_4874, plain, (![B_476, A_477]: (v1_relat_1(B_476) | ~m1_subset_1(B_476, k1_zfmisc_1(A_477)) | ~v1_relat_1(A_477))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.18/2.49  tff(c_4880, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_4874])).
% 7.18/2.49  tff(c_4887, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4880])).
% 7.18/2.49  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.18/2.49  tff(c_75, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 7.18/2.49  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.18/2.49  tff(c_5200, plain, (![A_516, B_517, C_518]: (k1_relset_1(A_516, B_517, C_518)=k1_relat_1(C_518) | ~m1_subset_1(C_518, k1_zfmisc_1(k2_zfmisc_1(A_516, B_517))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.18/2.49  tff(c_5223, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_5200])).
% 7.18/2.49  tff(c_5926, plain, (![B_597, A_598, C_599]: (k1_xboole_0=B_597 | k1_relset_1(A_598, B_597, C_599)=A_598 | ~v1_funct_2(C_599, A_598, B_597) | ~m1_subset_1(C_599, k1_zfmisc_1(k2_zfmisc_1(A_598, B_597))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.18/2.49  tff(c_5942, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_5926])).
% 7.18/2.49  tff(c_5958, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5223, c_5942])).
% 7.18/2.49  tff(c_5959, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_75, c_5958])).
% 7.18/2.49  tff(c_32, plain, (![B_23, A_22]: (k1_relat_1(k7_relat_1(B_23, A_22))=A_22 | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.18/2.49  tff(c_5978, plain, (![A_22]: (k1_relat_1(k7_relat_1('#skF_4', A_22))=A_22 | ~r1_tarski(A_22, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5959, c_32])).
% 7.18/2.49  tff(c_5984, plain, (![A_22]: (k1_relat_1(k7_relat_1('#skF_4', A_22))=A_22 | ~r1_tarski(A_22, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4887, c_5978])).
% 7.18/2.49  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.18/2.49  tff(c_5699, plain, (![A_580, B_581, C_582, D_583]: (k2_partfun1(A_580, B_581, C_582, D_583)=k7_relat_1(C_582, D_583) | ~m1_subset_1(C_582, k1_zfmisc_1(k2_zfmisc_1(A_580, B_581))) | ~v1_funct_1(C_582))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.18/2.49  tff(c_5708, plain, (![D_583]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_583)=k7_relat_1('#skF_4', D_583) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_5699])).
% 7.18/2.49  tff(c_5720, plain, (![D_583]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_583)=k7_relat_1('#skF_4', D_583))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5708])).
% 7.18/2.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.49  tff(c_865, plain, (![B_140, A_141]: (v1_relat_1(B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(A_141)) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.18/2.49  tff(c_871, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_865])).
% 7.18/2.49  tff(c_878, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_871])).
% 7.18/2.49  tff(c_1166, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.18/2.49  tff(c_1185, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1166])).
% 7.18/2.49  tff(c_1954, plain, (![B_278, A_279, C_280]: (k1_xboole_0=B_278 | k1_relset_1(A_279, B_278, C_280)=A_279 | ~v1_funct_2(C_280, A_279, B_278) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_279, B_278))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.18/2.49  tff(c_1967, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_1954])).
% 7.18/2.49  tff(c_1981, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1185, c_1967])).
% 7.18/2.49  tff(c_1982, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_75, c_1981])).
% 7.18/2.49  tff(c_2009, plain, (![A_22]: (k1_relat_1(k7_relat_1('#skF_4', A_22))=A_22 | ~r1_tarski(A_22, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1982, c_32])).
% 7.18/2.49  tff(c_2015, plain, (![A_22]: (k1_relat_1(k7_relat_1('#skF_4', A_22))=A_22 | ~r1_tarski(A_22, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_2009])).
% 7.18/2.49  tff(c_30, plain, (![B_21, A_20]: (r1_tarski(k7_relat_1(B_21, A_20), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.18/2.49  tff(c_133, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.18/2.49  tff(c_144, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_133])).
% 7.18/2.49  tff(c_924, plain, (![A_148, C_149, B_150]: (r1_tarski(A_148, C_149) | ~r1_tarski(B_150, C_149) | ~r1_tarski(A_148, B_150))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.18/2.49  tff(c_935, plain, (![A_148]: (r1_tarski(A_148, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_148, '#skF_4'))), inference(resolution, [status(thm)], [c_144, c_924])).
% 7.18/2.49  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.18/2.49  tff(c_1689, plain, (![D_258, B_259, C_260, A_261]: (m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(B_259, C_260))) | ~r1_tarski(k1_relat_1(D_258), B_259) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_261, C_260))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.18/2.49  tff(c_2899, plain, (![A_355, B_356, C_357, A_358]: (m1_subset_1(A_355, k1_zfmisc_1(k2_zfmisc_1(B_356, C_357))) | ~r1_tarski(k1_relat_1(A_355), B_356) | ~r1_tarski(A_355, k2_zfmisc_1(A_358, C_357)))), inference(resolution, [status(thm)], [c_22, c_1689])).
% 7.18/2.49  tff(c_4641, plain, (![A_464, B_465]: (m1_subset_1(A_464, k1_zfmisc_1(k2_zfmisc_1(B_465, '#skF_2'))) | ~r1_tarski(k1_relat_1(A_464), B_465) | ~r1_tarski(A_464, '#skF_4'))), inference(resolution, [status(thm)], [c_935, c_2899])).
% 7.18/2.49  tff(c_1595, plain, (![A_238, B_239, C_240, D_241]: (k2_partfun1(A_238, B_239, C_240, D_241)=k7_relat_1(C_240, D_241) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.18/2.49  tff(c_1602, plain, (![D_241]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_241)=k7_relat_1('#skF_4', D_241) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1595])).
% 7.18/2.49  tff(c_1611, plain, (![D_241]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_241)=k7_relat_1('#skF_4', D_241))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1602])).
% 7.18/2.49  tff(c_821, plain, (![A_134, B_135, C_136, D_137]: (v1_funct_1(k2_partfun1(A_134, B_135, C_136, D_137)) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.18/2.49  tff(c_828, plain, (![D_137]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_137)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_821])).
% 7.18/2.49  tff(c_837, plain, (![D_137]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_137)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_828])).
% 7.18/2.49  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.18/2.49  tff(c_153, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 7.18/2.49  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_837, c_153])).
% 7.18/2.49  tff(c_842, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 7.18/2.49  tff(c_844, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_842])).
% 7.18/2.49  tff(c_1616, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_844])).
% 7.18/2.49  tff(c_4682, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_4641, c_1616])).
% 7.18/2.49  tff(c_4741, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4682])).
% 7.18/2.49  tff(c_4744, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_4741])).
% 7.18/2.49  tff(c_4748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_4744])).
% 7.18/2.49  tff(c_4749, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_4682])).
% 7.18/2.49  tff(c_4848, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2015, c_4749])).
% 7.18/2.49  tff(c_4851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_6, c_4848])).
% 7.18/2.49  tff(c_4853, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_842])).
% 7.18/2.49  tff(c_5221, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_4853, c_5200])).
% 7.18/2.49  tff(c_5727, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5720, c_5720, c_5221])).
% 7.18/2.49  tff(c_4852, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_842])).
% 7.18/2.49  tff(c_5735, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5720, c_4852])).
% 7.18/2.49  tff(c_5734, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5720, c_4853])).
% 7.18/2.49  tff(c_6131, plain, (![B_603, C_604, A_605]: (k1_xboole_0=B_603 | v1_funct_2(C_604, A_605, B_603) | k1_relset_1(A_605, B_603, C_604)!=A_605 | ~m1_subset_1(C_604, k1_zfmisc_1(k2_zfmisc_1(A_605, B_603))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.18/2.49  tff(c_6137, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_5734, c_6131])).
% 7.18/2.49  tff(c_6160, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5735, c_75, c_6137])).
% 7.18/2.49  tff(c_6380, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5727, c_6160])).
% 7.18/2.49  tff(c_6387, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5984, c_6380])).
% 7.18/2.49  tff(c_6391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_6387])).
% 7.18/2.49  tff(c_6392, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 7.18/2.49  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.49  tff(c_6406, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_6392, c_16])).
% 7.18/2.49  tff(c_6393, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 7.18/2.49  tff(c_6398, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_6393])).
% 7.18/2.49  tff(c_6416, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6406, c_6398, c_62])).
% 7.18/2.49  tff(c_6872, plain, (![A_687, B_688]: (r1_tarski(A_687, B_688) | ~m1_subset_1(A_687, k1_zfmisc_1(B_688)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.18/2.49  tff(c_6883, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6416, c_6872])).
% 7.18/2.49  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.18/2.49  tff(c_6436, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_6392, c_10])).
% 7.18/2.49  tff(c_6888, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_6883, c_6436])).
% 7.18/2.49  tff(c_6399, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6398, c_64])).
% 7.18/2.49  tff(c_6896, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_6888, c_6399])).
% 7.18/2.49  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.18/2.49  tff(c_6404, plain, (![A_9]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_18])).
% 7.18/2.49  tff(c_6884, plain, (![A_9]: (r1_tarski('#skF_1', A_9))), inference(resolution, [status(thm)], [c_6404, c_6872])).
% 7.18/2.49  tff(c_6934, plain, (![A_9]: (r1_tarski('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_6884])).
% 7.18/2.49  tff(c_6407, plain, (![B_624]: (k2_zfmisc_1('#skF_1', B_624)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_6392, c_16])).
% 7.18/2.49  tff(c_6411, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6407, c_28])).
% 7.18/2.49  tff(c_6456, plain, (![B_628, A_629]: (r1_tarski(k7_relat_1(B_628, A_629), B_628) | ~v1_relat_1(B_628))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.18/2.49  tff(c_6460, plain, (![A_629]: (k7_relat_1('#skF_1', A_629)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6456, c_6436])).
% 7.18/2.49  tff(c_6463, plain, (![A_629]: (k7_relat_1('#skF_1', A_629)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6411, c_6460])).
% 7.18/2.49  tff(c_6891, plain, (![A_629]: (k7_relat_1('#skF_4', A_629)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_6888, c_6463])).
% 7.18/2.49  tff(c_6900, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_6404])).
% 7.18/2.49  tff(c_7467, plain, (![A_782, B_783, C_784, D_785]: (k2_partfun1(A_782, B_783, C_784, D_785)=k7_relat_1(C_784, D_785) | ~m1_subset_1(C_784, k1_zfmisc_1(k2_zfmisc_1(A_782, B_783))) | ~v1_funct_1(C_784))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.18/2.49  tff(c_7470, plain, (![A_782, B_783, D_785]: (k2_partfun1(A_782, B_783, '#skF_4', D_785)=k7_relat_1('#skF_4', D_785) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6900, c_7467])).
% 7.18/2.49  tff(c_7480, plain, (![A_782, B_783, D_785]: (k2_partfun1(A_782, B_783, '#skF_4', D_785)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6891, c_7470])).
% 7.18/2.49  tff(c_6479, plain, (![A_633, B_634]: (r1_tarski(A_633, B_634) | ~m1_subset_1(A_633, k1_zfmisc_1(B_634)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.18/2.49  tff(c_6490, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_6416, c_6479])).
% 7.18/2.49  tff(c_6495, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_6490, c_6436])).
% 7.18/2.49  tff(c_6507, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_6495, c_6404])).
% 7.18/2.49  tff(c_6852, plain, (![A_683, B_684, C_685, D_686]: (v1_funct_1(k2_partfun1(A_683, B_684, C_685, D_686)) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_683, B_684))) | ~v1_funct_1(C_685))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.18/2.49  tff(c_6855, plain, (![A_683, B_684, D_686]: (v1_funct_1(k2_partfun1(A_683, B_684, '#skF_4', D_686)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6507, c_6852])).
% 7.18/2.49  tff(c_6865, plain, (![A_683, B_684, D_686]: (v1_funct_1(k2_partfun1(A_683, B_684, '#skF_4', D_686)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6855])).
% 7.18/2.49  tff(c_6437, plain, (![A_626]: (A_626='#skF_1' | ~r1_tarski(A_626, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_6392, c_10])).
% 7.18/2.49  tff(c_6447, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_6437])).
% 7.18/2.49  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.18/2.49  tff(c_6417, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6392, c_6392, c_14])).
% 7.18/2.49  tff(c_6477, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6447, c_6398, c_6447, c_6447, c_6398, c_6398, c_6447, c_6417, c_6398, c_6398, c_56])).
% 7.18/2.49  tff(c_6478, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6477])).
% 7.18/2.49  tff(c_6497, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6495, c_6495, c_6495, c_6478])).
% 7.18/2.49  tff(c_6869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6865, c_6497])).
% 7.18/2.49  tff(c_6870, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_6477])).
% 7.18/2.49  tff(c_7020, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_6888, c_6888, c_6888, c_6888, c_6888, c_6888, c_6888, c_6888, c_6870])).
% 7.18/2.49  tff(c_7021, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7020])).
% 7.18/2.49  tff(c_7086, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_7021])).
% 7.18/2.49  tff(c_7483, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7480, c_7086])).
% 7.18/2.49  tff(c_7488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7483])).
% 7.18/2.49  tff(c_7490, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7020])).
% 7.18/2.49  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.18/2.49  tff(c_7534, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_7490, c_20])).
% 7.18/2.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.18/2.49  tff(c_7536, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_7534, c_2])).
% 7.18/2.49  tff(c_7545, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6934, c_7536])).
% 7.18/2.49  tff(c_7489, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_7020])).
% 7.18/2.49  tff(c_7553, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7545, c_7489])).
% 7.18/2.49  tff(c_7560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6896, c_7553])).
% 7.18/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.49  
% 7.18/2.49  Inference rules
% 7.18/2.49  ----------------------
% 7.18/2.49  #Ref     : 0
% 7.18/2.49  #Sup     : 1603
% 7.18/2.49  #Fact    : 0
% 7.18/2.49  #Define  : 0
% 7.18/2.49  #Split   : 31
% 7.18/2.49  #Chain   : 0
% 7.18/2.49  #Close   : 0
% 7.18/2.49  
% 7.18/2.49  Ordering : KBO
% 7.18/2.49  
% 7.18/2.49  Simplification rules
% 7.18/2.49  ----------------------
% 7.18/2.49  #Subsume      : 270
% 7.18/2.49  #Demod        : 1378
% 7.18/2.49  #Tautology    : 607
% 7.18/2.49  #SimpNegUnit  : 48
% 7.18/2.49  #BackRed      : 81
% 7.18/2.49  
% 7.18/2.49  #Partial instantiations: 0
% 7.18/2.49  #Strategies tried      : 1
% 7.18/2.49  
% 7.18/2.49  Timing (in seconds)
% 7.18/2.49  ----------------------
% 7.18/2.49  Preprocessing        : 0.35
% 7.18/2.49  Parsing              : 0.18
% 7.18/2.49  CNF conversion       : 0.02
% 7.18/2.49  Main loop            : 1.31
% 7.18/2.49  Inferencing          : 0.45
% 7.18/2.49  Reduction            : 0.45
% 7.18/2.49  Demodulation         : 0.32
% 7.18/2.49  BG Simplification    : 0.05
% 7.18/2.49  Subsumption          : 0.26
% 7.18/2.49  Abstraction          : 0.06
% 7.18/2.49  MUC search           : 0.00
% 7.18/2.49  Cooper               : 0.00
% 7.18/2.49  Total                : 1.71
% 7.18/2.49  Index Insertion      : 0.00
% 7.18/2.49  Index Deletion       : 0.00
% 7.18/2.49  Index Matching       : 0.00
% 7.18/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
