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
% DateTime   : Thu Dec  3 10:16:19 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.19s
% Verified   : 
% Statistics : Number of formulae       :  162 (1120 expanded)
%              Number of leaves         :   32 ( 377 expanded)
%              Depth                    :   17
%              Number of atoms          :  327 (3442 expanded)
%              Number of equality atoms :  141 ( 982 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_71,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_252,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_268,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_252])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_155,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_176,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_155])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_295,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_318,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_295])).

tff(c_541,plain,(
    ! [B_124,A_125,C_126] :
      ( k1_xboole_0 = B_124
      | k1_relset_1(A_125,B_124,C_126) = A_125
      | ~ v1_funct_2(C_126,A_125,B_124)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_551,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_541])).

tff(c_568,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_318,c_551])).

tff(c_578,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_175,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_155])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_317,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_295])).

tff(c_548,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_541])).

tff(c_565,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_317,c_548])).

tff(c_572,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_675,plain,(
    ! [A_136,B_137] :
      ( r2_hidden('#skF_1'(A_136,B_137),k1_relat_1(A_136))
      | B_137 = A_136
      | k1_relat_1(B_137) != k1_relat_1(A_136)
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_686,plain,(
    ! [B_137] :
      ( r2_hidden('#skF_1'('#skF_4',B_137),'#skF_2')
      | B_137 = '#skF_4'
      | k1_relat_1(B_137) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_675])).

tff(c_752,plain,(
    ! [B_143] :
      ( r2_hidden('#skF_1'('#skF_4',B_143),'#skF_2')
      | B_143 = '#skF_4'
      | k1_relat_1(B_143) != '#skF_2'
      | ~ v1_funct_1(B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_62,c_572,c_686])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_774,plain,(
    ! [B_147] :
      ( m1_subset_1('#skF_1'('#skF_4',B_147),'#skF_2')
      | B_147 = '#skF_4'
      | k1_relat_1(B_147) != '#skF_2'
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_752,c_16])).

tff(c_50,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ m1_subset_1(E_36,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1101,plain,(
    ! [B_165] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_165)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_165))
      | B_165 = '#skF_4'
      | k1_relat_1(B_165) != '#skF_2'
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(resolution,[status(thm)],[c_774,c_50])).

tff(c_24,plain,(
    ! [B_17,A_13] :
      ( k1_funct_1(B_17,'#skF_1'(A_13,B_17)) != k1_funct_1(A_13,'#skF_1'(A_13,B_17))
      | B_17 = A_13
      | k1_relat_1(B_17) != k1_relat_1(A_13)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1108,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_24])).

tff(c_1115,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_56,c_578,c_175,c_62,c_578,c_572,c_1108])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1132,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_48])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_1132])).

tff(c_1144,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_95])).

tff(c_1170,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_107])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1172,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1144,c_10])).

tff(c_106,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_114,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_106,c_114])).

tff(c_335,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_1279,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_335])).

tff(c_1289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_1279])).

tff(c_1290,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_1316,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_107])).

tff(c_1318,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_1290,c_10])).

tff(c_1422,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_335])).

tff(c_1432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_1422])).

tff(c_1433,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_1441,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_52])).

tff(c_1668,plain,(
    ! [B_207,A_208,C_209] :
      ( k1_xboole_0 = B_207
      | k1_relset_1(A_208,B_207,C_209) = A_208
      | ~ v1_funct_2(C_209,A_208,B_207)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1671,plain,(
    ! [C_209] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_209) = '#skF_2'
      | ~ v1_funct_2(C_209,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_209,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_1668])).

tff(c_1821,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1671])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1457,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1433,c_8])).

tff(c_1508,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1457])).

tff(c_1834,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_1508])).

tff(c_1850,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_1821,c_10])).

tff(c_1949,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_1433])).

tff(c_1951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1834,c_1949])).

tff(c_1954,plain,(
    ! [C_232] :
      ( k1_relset_1('#skF_2','#skF_3',C_232) = '#skF_2'
      | ~ v1_funct_2(C_232,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_232,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_1671])).

tff(c_1957,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1441,c_1954])).

tff(c_1971,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_318,c_1957])).

tff(c_1440,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_58])).

tff(c_1960,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1440,c_1954])).

tff(c_1974,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_317,c_1960])).

tff(c_2247,plain,(
    ! [A_251,B_252] :
      ( r2_hidden('#skF_1'(A_251,B_252),k1_relat_1(A_251))
      | B_252 = A_251
      | k1_relat_1(B_252) != k1_relat_1(A_251)
      | ~ v1_funct_1(B_252)
      | ~ v1_relat_1(B_252)
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2255,plain,(
    ! [B_252] :
      ( r2_hidden('#skF_1'('#skF_4',B_252),'#skF_2')
      | B_252 = '#skF_4'
      | k1_relat_1(B_252) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_252)
      | ~ v1_relat_1(B_252)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1974,c_2247])).

tff(c_2295,plain,(
    ! [B_255] :
      ( r2_hidden('#skF_1'('#skF_4',B_255),'#skF_2')
      | B_255 = '#skF_4'
      | k1_relat_1(B_255) != '#skF_2'
      | ~ v1_funct_1(B_255)
      | ~ v1_relat_1(B_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_62,c_1974,c_2255])).

tff(c_2311,plain,(
    ! [B_257] :
      ( m1_subset_1('#skF_1'('#skF_4',B_257),'#skF_2')
      | B_257 = '#skF_4'
      | k1_relat_1(B_257) != '#skF_2'
      | ~ v1_funct_1(B_257)
      | ~ v1_relat_1(B_257) ) ),
    inference(resolution,[status(thm)],[c_2295,c_16])).

tff(c_2654,plain,(
    ! [B_274] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_274)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_274))
      | B_274 = '#skF_4'
      | k1_relat_1(B_274) != '#skF_2'
      | ~ v1_funct_1(B_274)
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_2311,c_50])).

tff(c_2661,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2654,c_24])).

tff(c_2668,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_56,c_1971,c_175,c_62,c_1974,c_1971,c_2661])).

tff(c_105,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_95])).

tff(c_124,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_114])).

tff(c_272,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_1435,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_272])).

tff(c_2693,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2668,c_1435])).

tff(c_2706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2693])).

tff(c_2708,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1457])).

tff(c_2722,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2708,c_107])).

tff(c_2750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2722,c_1435])).

tff(c_2751,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_2758,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_52])).

tff(c_2846,plain,(
    ! [A_281,B_282,C_283] :
      ( k1_relset_1(A_281,B_282,C_283) = k1_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2943,plain,(
    ! [C_304] :
      ( k1_relset_1('#skF_2','#skF_3',C_304) = k1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_2846])).

tff(c_2958,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2758,c_2943])).

tff(c_3065,plain,(
    ! [B_318,C_319,A_320] :
      ( k1_xboole_0 = B_318
      | v1_funct_2(C_319,A_320,B_318)
      | k1_relset_1(A_320,B_318,C_319) != A_320
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_320,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3068,plain,(
    ! [C_319] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_319,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_319) != '#skF_2'
      | ~ m1_subset_1(C_319,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_3065])).

tff(c_3153,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3068])).

tff(c_2771,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_8])).

tff(c_2823,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2771])).

tff(c_3192,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3153,c_2823])).

tff(c_3241,plain,(
    ! [A_334] : k2_zfmisc_1(A_334,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3153,c_3153,c_10])).

tff(c_3262,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3241,c_2751])).

tff(c_3280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3192,c_3262])).

tff(c_3282,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3068])).

tff(c_3305,plain,(
    ! [B_336,A_337,C_338] :
      ( k1_xboole_0 = B_336
      | k1_relset_1(A_337,B_336,C_338) = A_337
      | ~ v1_funct_2(C_338,A_337,B_336)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_337,B_336))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3308,plain,(
    ! [C_338] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_338) = '#skF_2'
      | ~ v1_funct_2(C_338,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_338,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2751,c_3305])).

tff(c_3347,plain,(
    ! [C_341] :
      ( k1_relset_1('#skF_2','#skF_3',C_341) = '#skF_2'
      | ~ v1_funct_2(C_341,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_341,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3282,c_3308])).

tff(c_3350,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2758,c_3347])).

tff(c_3364,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2958,c_3350])).

tff(c_2757,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_58])).

tff(c_2959,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2757,c_2943])).

tff(c_3353,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2757,c_3347])).

tff(c_3367,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2959,c_3353])).

tff(c_3497,plain,(
    ! [A_351,B_352] :
      ( r2_hidden('#skF_1'(A_351,B_352),k1_relat_1(A_351))
      | B_352 = A_351
      | k1_relat_1(B_352) != k1_relat_1(A_351)
      | ~ v1_funct_1(B_352)
      | ~ v1_relat_1(B_352)
      | ~ v1_funct_1(A_351)
      | ~ v1_relat_1(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3505,plain,(
    ! [B_352] :
      ( r2_hidden('#skF_1'('#skF_4',B_352),'#skF_2')
      | B_352 = '#skF_4'
      | k1_relat_1(B_352) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_352)
      | ~ v1_relat_1(B_352)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3367,c_3497])).

tff(c_3596,plain,(
    ! [B_359] :
      ( r2_hidden('#skF_1'('#skF_4',B_359),'#skF_2')
      | B_359 = '#skF_4'
      | k1_relat_1(B_359) != '#skF_2'
      | ~ v1_funct_1(B_359)
      | ~ v1_relat_1(B_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_62,c_3367,c_3505])).

tff(c_3615,plain,(
    ! [B_363] :
      ( m1_subset_1('#skF_1'('#skF_4',B_363),'#skF_2')
      | B_363 = '#skF_4'
      | k1_relat_1(B_363) != '#skF_2'
      | ~ v1_funct_1(B_363)
      | ~ v1_relat_1(B_363) ) ),
    inference(resolution,[status(thm)],[c_3596,c_16])).

tff(c_3644,plain,(
    ! [B_367] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_367)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_367))
      | B_367 = '#skF_4'
      | k1_relat_1(B_367) != '#skF_2'
      | ~ v1_funct_1(B_367)
      | ~ v1_relat_1(B_367) ) ),
    inference(resolution,[status(thm)],[c_3615,c_50])).

tff(c_3651,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3644,c_24])).

tff(c_3658,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_56,c_3364,c_175,c_62,c_3367,c_3364,c_3651])).

tff(c_2755,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2751,c_106])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2778,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2755,c_2])).

tff(c_2803,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2778])).

tff(c_3666,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_2803])).

tff(c_3679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3666])).

tff(c_3681,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2771])).

tff(c_3690,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3681,c_107])).

tff(c_3702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3690,c_2803])).

tff(c_3703,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2778])).

tff(c_3710,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3703,c_48])).

tff(c_3719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_3710])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/1.94  
% 5.19/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/1.95  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.19/1.95  
% 5.19/1.95  %Foreground sorts:
% 5.19/1.95  
% 5.19/1.95  
% 5.19/1.95  %Background operators:
% 5.19/1.95  
% 5.19/1.95  
% 5.19/1.95  %Foreground operators:
% 5.19/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.19/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.19/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.19/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.19/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.19/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.19/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.19/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.19/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.19/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.19/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.19/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.19/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/1.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.19/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.19/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/1.95  
% 5.19/1.97  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 5.19/1.97  tff(f_87, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.19/1.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.19/1.97  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.19/1.97  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.19/1.97  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.19/1.97  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.19/1.97  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.19/1.97  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.19/1.97  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.19/1.97  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.19/1.97  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_252, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.19/1.97  tff(c_268, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_252])).
% 5.19/1.97  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.19/1.97  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_155, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.19/1.97  tff(c_176, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_155])).
% 5.19/1.97  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_295, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.19/1.97  tff(c_318, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_295])).
% 5.19/1.97  tff(c_541, plain, (![B_124, A_125, C_126]: (k1_xboole_0=B_124 | k1_relset_1(A_125, B_124, C_126)=A_125 | ~v1_funct_2(C_126, A_125, B_124) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.19/1.97  tff(c_551, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_541])).
% 5.19/1.97  tff(c_568, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_318, c_551])).
% 5.19/1.97  tff(c_578, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_568])).
% 5.19/1.97  tff(c_175, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_155])).
% 5.19/1.97  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_317, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_295])).
% 5.19/1.97  tff(c_548, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_541])).
% 5.19/1.97  tff(c_565, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_317, c_548])).
% 5.19/1.97  tff(c_572, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_565])).
% 5.19/1.97  tff(c_675, plain, (![A_136, B_137]: (r2_hidden('#skF_1'(A_136, B_137), k1_relat_1(A_136)) | B_137=A_136 | k1_relat_1(B_137)!=k1_relat_1(A_136) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.19/1.97  tff(c_686, plain, (![B_137]: (r2_hidden('#skF_1'('#skF_4', B_137), '#skF_2') | B_137='#skF_4' | k1_relat_1(B_137)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_137) | ~v1_relat_1(B_137) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_572, c_675])).
% 5.19/1.97  tff(c_752, plain, (![B_143]: (r2_hidden('#skF_1'('#skF_4', B_143), '#skF_2') | B_143='#skF_4' | k1_relat_1(B_143)!='#skF_2' | ~v1_funct_1(B_143) | ~v1_relat_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_62, c_572, c_686])).
% 5.19/1.97  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.19/1.97  tff(c_774, plain, (![B_147]: (m1_subset_1('#skF_1'('#skF_4', B_147), '#skF_2') | B_147='#skF_4' | k1_relat_1(B_147)!='#skF_2' | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_752, c_16])).
% 5.19/1.97  tff(c_50, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~m1_subset_1(E_36, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_1101, plain, (![B_165]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_165))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_165)) | B_165='#skF_4' | k1_relat_1(B_165)!='#skF_2' | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(resolution, [status(thm)], [c_774, c_50])).
% 5.19/1.97  tff(c_24, plain, (![B_17, A_13]: (k1_funct_1(B_17, '#skF_1'(A_13, B_17))!=k1_funct_1(A_13, '#skF_1'(A_13, B_17)) | B_17=A_13 | k1_relat_1(B_17)!=k1_relat_1(A_13) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.19/1.97  tff(c_1108, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1101, c_24])).
% 5.19/1.97  tff(c_1115, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_56, c_578, c_175, c_62, c_578, c_572, c_1108])).
% 5.19/1.97  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.19/1.97  tff(c_1132, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_48])).
% 5.19/1.97  tff(c_1143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_1132])).
% 5.19/1.97  tff(c_1144, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_568])).
% 5.19/1.97  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.19/1.97  tff(c_95, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.19/1.97  tff(c_107, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_95])).
% 5.19/1.97  tff(c_1170, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_107])).
% 5.19/1.97  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.19/1.97  tff(c_1172, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1144, c_10])).
% 5.19/1.97  tff(c_106, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_95])).
% 5.19/1.97  tff(c_114, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.19/1.97  tff(c_123, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_106, c_114])).
% 5.19/1.97  tff(c_335, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_123])).
% 5.19/1.97  tff(c_1279, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_335])).
% 5.19/1.97  tff(c_1289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1170, c_1279])).
% 5.19/1.97  tff(c_1290, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_565])).
% 5.19/1.97  tff(c_1316, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_107])).
% 5.19/1.97  tff(c_1318, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1290, c_1290, c_10])).
% 5.19/1.97  tff(c_1422, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_335])).
% 5.19/1.97  tff(c_1432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1316, c_1422])).
% 5.19/1.97  tff(c_1433, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_123])).
% 5.19/1.97  tff(c_1441, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_52])).
% 5.19/1.97  tff(c_1668, plain, (![B_207, A_208, C_209]: (k1_xboole_0=B_207 | k1_relset_1(A_208, B_207, C_209)=A_208 | ~v1_funct_2(C_209, A_208, B_207) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.19/1.97  tff(c_1671, plain, (![C_209]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_209)='#skF_2' | ~v1_funct_2(C_209, '#skF_2', '#skF_3') | ~m1_subset_1(C_209, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1433, c_1668])).
% 5.19/1.97  tff(c_1821, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1671])).
% 5.19/1.97  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.19/1.97  tff(c_1457, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1433, c_8])).
% 5.19/1.97  tff(c_1508, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_1457])).
% 5.19/1.97  tff(c_1834, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_1508])).
% 5.19/1.97  tff(c_1850, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1821, c_1821, c_10])).
% 5.19/1.97  tff(c_1949, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1850, c_1433])).
% 5.19/1.97  tff(c_1951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1834, c_1949])).
% 5.19/1.97  tff(c_1954, plain, (![C_232]: (k1_relset_1('#skF_2', '#skF_3', C_232)='#skF_2' | ~v1_funct_2(C_232, '#skF_2', '#skF_3') | ~m1_subset_1(C_232, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1671])).
% 5.19/1.97  tff(c_1957, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1441, c_1954])).
% 5.19/1.97  tff(c_1971, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_318, c_1957])).
% 5.19/1.97  tff(c_1440, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_58])).
% 5.19/1.97  tff(c_1960, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1440, c_1954])).
% 5.19/1.97  tff(c_1974, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_317, c_1960])).
% 5.19/1.97  tff(c_2247, plain, (![A_251, B_252]: (r2_hidden('#skF_1'(A_251, B_252), k1_relat_1(A_251)) | B_252=A_251 | k1_relat_1(B_252)!=k1_relat_1(A_251) | ~v1_funct_1(B_252) | ~v1_relat_1(B_252) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.19/1.97  tff(c_2255, plain, (![B_252]: (r2_hidden('#skF_1'('#skF_4', B_252), '#skF_2') | B_252='#skF_4' | k1_relat_1(B_252)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_252) | ~v1_relat_1(B_252) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1974, c_2247])).
% 5.19/1.97  tff(c_2295, plain, (![B_255]: (r2_hidden('#skF_1'('#skF_4', B_255), '#skF_2') | B_255='#skF_4' | k1_relat_1(B_255)!='#skF_2' | ~v1_funct_1(B_255) | ~v1_relat_1(B_255))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_62, c_1974, c_2255])).
% 5.19/1.97  tff(c_2311, plain, (![B_257]: (m1_subset_1('#skF_1'('#skF_4', B_257), '#skF_2') | B_257='#skF_4' | k1_relat_1(B_257)!='#skF_2' | ~v1_funct_1(B_257) | ~v1_relat_1(B_257))), inference(resolution, [status(thm)], [c_2295, c_16])).
% 5.19/1.97  tff(c_2654, plain, (![B_274]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_274))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_274)) | B_274='#skF_4' | k1_relat_1(B_274)!='#skF_2' | ~v1_funct_1(B_274) | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_2311, c_50])).
% 5.19/1.97  tff(c_2661, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2654, c_24])).
% 5.19/1.97  tff(c_2668, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_56, c_1971, c_175, c_62, c_1974, c_1971, c_2661])).
% 5.19/1.97  tff(c_105, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_95])).
% 5.19/1.97  tff(c_124, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_105, c_114])).
% 5.19/1.97  tff(c_272, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_124])).
% 5.19/1.97  tff(c_1435, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_272])).
% 5.19/1.97  tff(c_2693, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2668, c_1435])).
% 5.19/1.97  tff(c_2706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2693])).
% 5.19/1.97  tff(c_2708, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1457])).
% 5.19/1.97  tff(c_2722, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2708, c_107])).
% 5.19/1.97  tff(c_2750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2722, c_1435])).
% 5.19/1.97  tff(c_2751, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_124])).
% 5.19/1.97  tff(c_2758, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_52])).
% 5.19/1.97  tff(c_2846, plain, (![A_281, B_282, C_283]: (k1_relset_1(A_281, B_282, C_283)=k1_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.19/1.97  tff(c_2943, plain, (![C_304]: (k1_relset_1('#skF_2', '#skF_3', C_304)=k1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_2846])).
% 5.19/1.97  tff(c_2958, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2758, c_2943])).
% 5.19/1.97  tff(c_3065, plain, (![B_318, C_319, A_320]: (k1_xboole_0=B_318 | v1_funct_2(C_319, A_320, B_318) | k1_relset_1(A_320, B_318, C_319)!=A_320 | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_320, B_318))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.19/1.97  tff(c_3068, plain, (![C_319]: (k1_xboole_0='#skF_3' | v1_funct_2(C_319, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_319)!='#skF_2' | ~m1_subset_1(C_319, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_3065])).
% 5.19/1.97  tff(c_3153, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3068])).
% 5.19/1.97  tff(c_2771, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2751, c_8])).
% 5.19/1.97  tff(c_2823, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2771])).
% 5.19/1.97  tff(c_3192, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3153, c_2823])).
% 5.19/1.97  tff(c_3241, plain, (![A_334]: (k2_zfmisc_1(A_334, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3153, c_3153, c_10])).
% 5.19/1.97  tff(c_3262, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3241, c_2751])).
% 5.19/1.97  tff(c_3280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3192, c_3262])).
% 5.19/1.97  tff(c_3282, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3068])).
% 5.19/1.97  tff(c_3305, plain, (![B_336, A_337, C_338]: (k1_xboole_0=B_336 | k1_relset_1(A_337, B_336, C_338)=A_337 | ~v1_funct_2(C_338, A_337, B_336) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_337, B_336))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.19/1.97  tff(c_3308, plain, (![C_338]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_338)='#skF_2' | ~v1_funct_2(C_338, '#skF_2', '#skF_3') | ~m1_subset_1(C_338, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2751, c_3305])).
% 5.19/1.97  tff(c_3347, plain, (![C_341]: (k1_relset_1('#skF_2', '#skF_3', C_341)='#skF_2' | ~v1_funct_2(C_341, '#skF_2', '#skF_3') | ~m1_subset_1(C_341, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_3282, c_3308])).
% 5.19/1.97  tff(c_3350, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2758, c_3347])).
% 5.19/1.97  tff(c_3364, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2958, c_3350])).
% 5.19/1.97  tff(c_2757, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_58])).
% 5.19/1.97  tff(c_2959, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2757, c_2943])).
% 5.19/1.97  tff(c_3353, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2757, c_3347])).
% 5.19/1.97  tff(c_3367, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2959, c_3353])).
% 5.19/1.97  tff(c_3497, plain, (![A_351, B_352]: (r2_hidden('#skF_1'(A_351, B_352), k1_relat_1(A_351)) | B_352=A_351 | k1_relat_1(B_352)!=k1_relat_1(A_351) | ~v1_funct_1(B_352) | ~v1_relat_1(B_352) | ~v1_funct_1(A_351) | ~v1_relat_1(A_351))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.19/1.97  tff(c_3505, plain, (![B_352]: (r2_hidden('#skF_1'('#skF_4', B_352), '#skF_2') | B_352='#skF_4' | k1_relat_1(B_352)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_352) | ~v1_relat_1(B_352) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3367, c_3497])).
% 5.19/1.97  tff(c_3596, plain, (![B_359]: (r2_hidden('#skF_1'('#skF_4', B_359), '#skF_2') | B_359='#skF_4' | k1_relat_1(B_359)!='#skF_2' | ~v1_funct_1(B_359) | ~v1_relat_1(B_359))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_62, c_3367, c_3505])).
% 5.19/1.97  tff(c_3615, plain, (![B_363]: (m1_subset_1('#skF_1'('#skF_4', B_363), '#skF_2') | B_363='#skF_4' | k1_relat_1(B_363)!='#skF_2' | ~v1_funct_1(B_363) | ~v1_relat_1(B_363))), inference(resolution, [status(thm)], [c_3596, c_16])).
% 5.19/1.97  tff(c_3644, plain, (![B_367]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_367))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_367)) | B_367='#skF_4' | k1_relat_1(B_367)!='#skF_2' | ~v1_funct_1(B_367) | ~v1_relat_1(B_367))), inference(resolution, [status(thm)], [c_3615, c_50])).
% 5.19/1.97  tff(c_3651, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3644, c_24])).
% 5.19/1.97  tff(c_3658, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_56, c_3364, c_175, c_62, c_3367, c_3364, c_3651])).
% 5.19/1.97  tff(c_2755, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2751, c_106])).
% 5.19/1.97  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.19/1.97  tff(c_2778, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2755, c_2])).
% 5.19/1.97  tff(c_2803, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_2778])).
% 5.19/1.97  tff(c_3666, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_2803])).
% 5.19/1.97  tff(c_3679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3666])).
% 5.19/1.97  tff(c_3681, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2771])).
% 5.19/1.97  tff(c_3690, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3681, c_107])).
% 5.19/1.97  tff(c_3702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3690, c_2803])).
% 5.19/1.97  tff(c_3703, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2778])).
% 5.19/1.97  tff(c_3710, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3703, c_48])).
% 5.19/1.97  tff(c_3719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_3710])).
% 5.19/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.19/1.97  
% 5.19/1.97  Inference rules
% 5.19/1.97  ----------------------
% 5.19/1.97  #Ref     : 3
% 5.19/1.97  #Sup     : 710
% 5.19/1.97  #Fact    : 0
% 5.19/1.97  #Define  : 0
% 5.19/1.97  #Split   : 18
% 5.19/1.97  #Chain   : 0
% 5.19/1.97  #Close   : 0
% 5.19/1.97  
% 5.19/1.97  Ordering : KBO
% 5.19/1.97  
% 5.19/1.97  Simplification rules
% 5.19/1.97  ----------------------
% 5.19/1.97  #Subsume      : 136
% 5.19/1.97  #Demod        : 916
% 5.19/1.97  #Tautology    : 335
% 5.19/1.97  #SimpNegUnit  : 44
% 5.19/1.97  #BackRed      : 252
% 5.19/1.97  
% 5.19/1.97  #Partial instantiations: 0
% 5.19/1.97  #Strategies tried      : 1
% 5.19/1.97  
% 5.19/1.97  Timing (in seconds)
% 5.19/1.97  ----------------------
% 5.19/1.97  Preprocessing        : 0.34
% 5.19/1.97  Parsing              : 0.18
% 5.19/1.97  CNF conversion       : 0.02
% 5.19/1.97  Main loop            : 0.86
% 5.19/1.97  Inferencing          : 0.28
% 5.46/1.97  Reduction            : 0.30
% 5.46/1.97  Demodulation         : 0.21
% 5.46/1.97  BG Simplification    : 0.04
% 5.46/1.97  Subsumption          : 0.17
% 5.46/1.97  Abstraction          : 0.04
% 5.46/1.97  MUC search           : 0.00
% 5.46/1.97  Cooper               : 0.00
% 5.46/1.97  Total                : 1.25
% 5.46/1.97  Index Insertion      : 0.00
% 5.46/1.97  Index Deletion       : 0.00
% 5.46/1.98  Index Matching       : 0.00
% 5.46/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
