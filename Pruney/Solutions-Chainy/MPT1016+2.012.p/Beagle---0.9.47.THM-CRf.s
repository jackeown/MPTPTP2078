%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 485 expanded)
%              Number of leaves         :   34 ( 172 expanded)
%              Depth                    :   14
%              Number of atoms          :  248 (1445 expanded)
%              Number of equality atoms :   61 ( 308 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_101,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_143,plain,(
    ! [A_64] :
      ( '#skF_2'(A_64) != '#skF_1'(A_64)
      | v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_64])).

tff(c_149,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40,c_146])).

tff(c_257,plain,(
    ! [A_83] :
      ( k1_funct_1(A_83,'#skF_2'(A_83)) = k1_funct_1(A_83,'#skF_1'(A_83))
      | v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    ! [D_38,C_37] :
      ( v2_funct_1('#skF_4')
      | D_38 = C_37
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_127,plain,(
    ! [D_38,C_37] :
      ( D_38 = C_37
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60])).

tff(c_266,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_127])).

tff(c_275,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40,c_266])).

tff(c_276,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_275])).

tff(c_392,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_166,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_175,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_196,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1(k1_relset_1(A_77,B_78,C_79),k1_zfmisc_1(A_77))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_212,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_196])).

tff(c_218,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_212])).

tff(c_152,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_2'(A_69),k1_relat_1(A_69))
      | v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_850,plain,(
    ! [A_140,A_141] :
      ( r2_hidden('#skF_2'(A_140),A_141)
      | ~ m1_subset_1(k1_relat_1(A_140),k1_zfmisc_1(A_141))
      | v2_funct_1(A_140)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_152,c_10])).

tff(c_859,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_218,c_850])).

tff(c_870,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40,c_859])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_392,c_870])).

tff(c_874,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_263,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_127])).

tff(c_272,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40,c_263])).

tff(c_273,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_272])).

tff(c_903,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_273])).

tff(c_906,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_903])).

tff(c_907,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_906])).

tff(c_159,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_1'(A_70),k1_relat_1(A_70))
      | v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1490,plain,(
    ! [A_212,A_213] :
      ( r2_hidden('#skF_1'(A_212),A_213)
      | ~ m1_subset_1(k1_relat_1(A_212),k1_zfmisc_1(A_213))
      | v2_funct_1(A_212)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_159,c_10])).

tff(c_1499,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_218,c_1490])).

tff(c_1510,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_40,c_1499])).

tff(c_1512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_907,c_1510])).

tff(c_1514,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1518,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_46])).

tff(c_2025,plain,(
    ! [D_287,C_288,B_289,A_290] :
      ( k1_funct_1(k2_funct_1(D_287),k1_funct_1(D_287,C_288)) = C_288
      | k1_xboole_0 = B_289
      | ~ r2_hidden(C_288,A_290)
      | ~ v2_funct_1(D_287)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(A_290,B_289)))
      | ~ v1_funct_2(D_287,A_290,B_289)
      | ~ v1_funct_1(D_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2047,plain,(
    ! [D_291,B_292] :
      ( k1_funct_1(k2_funct_1(D_291),k1_funct_1(D_291,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_292
      | ~ v2_funct_1(D_291)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_292)))
      | ~ v1_funct_2(D_291,'#skF_3',B_292)
      | ~ v1_funct_1(D_291) ) ),
    inference(resolution,[status(thm)],[c_1518,c_2025])).

tff(c_2058,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2047])).

tff(c_2064,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1514,c_2058])).

tff(c_2066,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2064])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1516,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_48])).

tff(c_1589,plain,(
    ! [C_229,A_230,B_231] :
      ( r2_hidden(C_229,A_230)
      | ~ r2_hidden(C_229,B_231)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(A_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1596,plain,(
    ! [A_232] :
      ( r2_hidden('#skF_5',A_232)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_232)) ) ),
    inference(resolution,[status(thm)],[c_1516,c_1589])).

tff(c_1601,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_5',B_9)
      | ~ r1_tarski('#skF_3',B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_1596])).

tff(c_1618,plain,(
    ! [A_237,C_238,B_239] :
      ( m1_subset_1(A_237,C_238)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(C_238))
      | ~ r2_hidden(A_237,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1630,plain,(
    ! [A_242,B_243,A_244] :
      ( m1_subset_1(A_242,B_243)
      | ~ r2_hidden(A_242,A_244)
      | ~ r1_tarski(A_244,B_243) ) ),
    inference(resolution,[status(thm)],[c_14,c_1618])).

tff(c_1659,plain,(
    ! [B_247,B_248] :
      ( m1_subset_1('#skF_5',B_247)
      | ~ r1_tarski(B_248,B_247)
      | ~ r1_tarski('#skF_3',B_248) ) ),
    inference(resolution,[status(thm)],[c_1601,c_1630])).

tff(c_1668,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_5',A_3)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1659])).

tff(c_1669,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1668])).

tff(c_2074,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2066,c_1669])).

tff(c_2080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2074])).

tff(c_2082,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2064])).

tff(c_1513,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2081,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2064])).

tff(c_44,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1530,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_44])).

tff(c_2149,plain,(
    ! [D_299,B_300] :
      ( k1_funct_1(k2_funct_1(D_299),k1_funct_1(D_299,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_300
      | ~ v2_funct_1(D_299)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_300)))
      | ~ v1_funct_2(D_299,'#skF_3',B_300)
      | ~ v1_funct_1(D_299) ) ),
    inference(resolution,[status(thm)],[c_1516,c_2025])).

tff(c_2160,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2149])).

tff(c_2166,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1514,c_2081,c_1530,c_2160])).

tff(c_2168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2082,c_1513,c_2166])).

tff(c_2174,plain,(
    ! [A_301] : m1_subset_1('#skF_5',A_301) ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2188,plain,(
    ! [B_9] : r1_tarski('#skF_5',B_9) ),
    inference(resolution,[status(thm)],[c_2174,c_12])).

tff(c_2170,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_1535,plain,(
    ! [B_218,A_219] :
      ( B_218 = A_219
      | ~ r1_tarski(B_218,A_219)
      | ~ r1_tarski(A_219,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1547,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1535])).

tff(c_2198,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2170,c_1547])).

tff(c_2315,plain,(
    ! [A_312] :
      ( A_312 = '#skF_3'
      | ~ r1_tarski(A_312,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_2198,c_1547])).

tff(c_2333,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2188,c_2315])).

tff(c_2343,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2333,c_1513])).

tff(c_2205,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_8])).

tff(c_1644,plain,(
    ! [B_243] :
      ( m1_subset_1('#skF_6',B_243)
      | ~ r1_tarski('#skF_3',B_243) ) ),
    inference(resolution,[status(thm)],[c_1518,c_1630])).

tff(c_2238,plain,(
    ! [B_304] : m1_subset_1('#skF_6',B_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2205,c_1644])).

tff(c_2252,plain,(
    ! [B_9] : r1_tarski('#skF_6',B_9) ),
    inference(resolution,[status(thm)],[c_2238,c_12])).

tff(c_2332,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2252,c_2315])).

tff(c_2352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2343,c_2332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:53:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.73  
% 4.28/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.28/1.73  
% 4.28/1.73  %Foreground sorts:
% 4.28/1.73  
% 4.28/1.73  
% 4.28/1.73  %Background operators:
% 4.28/1.73  
% 4.28/1.73  
% 4.28/1.73  %Foreground operators:
% 4.28/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.28/1.73  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.28/1.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.28/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.28/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.28/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.28/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.28/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.28/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.28/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.28/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.28/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.28/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.28/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.28/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.73  
% 4.28/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.28/1.77  tff(f_109, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 4.28/1.77  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.28/1.77  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 4.28/1.77  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.28/1.77  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.28/1.77  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.28/1.77  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 4.28/1.77  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.28/1.77  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.28/1.77  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.28/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.77  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_42, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_64, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 4.28/1.77  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_101, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.28/1.77  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_101])).
% 4.28/1.77  tff(c_143, plain, (![A_64]: ('#skF_2'(A_64)!='#skF_1'(A_64) | v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.28/1.77  tff(c_146, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_143, c_64])).
% 4.28/1.77  tff(c_149, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40, c_146])).
% 4.28/1.77  tff(c_257, plain, (![A_83]: (k1_funct_1(A_83, '#skF_2'(A_83))=k1_funct_1(A_83, '#skF_1'(A_83)) | v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.28/1.77  tff(c_60, plain, (![D_38, C_37]: (v2_funct_1('#skF_4') | D_38=C_37 | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_127, plain, (![D_38, C_37]: (D_38=C_37 | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_60])).
% 4.28/1.77  tff(c_266, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_127])).
% 4.28/1.77  tff(c_275, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40, c_266])).
% 4.28/1.77  tff(c_276, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_275])).
% 4.28/1.77  tff(c_392, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_276])).
% 4.28/1.77  tff(c_166, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.28/1.77  tff(c_175, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_166])).
% 4.28/1.77  tff(c_196, plain, (![A_77, B_78, C_79]: (m1_subset_1(k1_relset_1(A_77, B_78, C_79), k1_zfmisc_1(A_77)) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.28/1.77  tff(c_212, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_175, c_196])).
% 4.28/1.77  tff(c_218, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_212])).
% 4.28/1.77  tff(c_152, plain, (![A_69]: (r2_hidden('#skF_2'(A_69), k1_relat_1(A_69)) | v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.28/1.77  tff(c_10, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.28/1.77  tff(c_850, plain, (![A_140, A_141]: (r2_hidden('#skF_2'(A_140), A_141) | ~m1_subset_1(k1_relat_1(A_140), k1_zfmisc_1(A_141)) | v2_funct_1(A_140) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_152, c_10])).
% 4.28/1.77  tff(c_859, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_218, c_850])).
% 4.28/1.77  tff(c_870, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40, c_859])).
% 4.28/1.77  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_392, c_870])).
% 4.28/1.77  tff(c_874, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_276])).
% 4.28/1.77  tff(c_263, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_127])).
% 4.28/1.77  tff(c_272, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40, c_263])).
% 4.28/1.77  tff(c_273, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_272])).
% 4.28/1.77  tff(c_903, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_37, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_874, c_273])).
% 4.28/1.77  tff(c_906, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_903])).
% 4.28/1.77  tff(c_907, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_149, c_906])).
% 4.28/1.77  tff(c_159, plain, (![A_70]: (r2_hidden('#skF_1'(A_70), k1_relat_1(A_70)) | v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.28/1.77  tff(c_1490, plain, (![A_212, A_213]: (r2_hidden('#skF_1'(A_212), A_213) | ~m1_subset_1(k1_relat_1(A_212), k1_zfmisc_1(A_213)) | v2_funct_1(A_212) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_159, c_10])).
% 4.28/1.77  tff(c_1499, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_218, c_1490])).
% 4.28/1.77  tff(c_1510, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_40, c_1499])).
% 4.28/1.77  tff(c_1512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_907, c_1510])).
% 4.28/1.77  tff(c_1514, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 4.28/1.77  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_1518, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_46])).
% 4.28/1.77  tff(c_2025, plain, (![D_287, C_288, B_289, A_290]: (k1_funct_1(k2_funct_1(D_287), k1_funct_1(D_287, C_288))=C_288 | k1_xboole_0=B_289 | ~r2_hidden(C_288, A_290) | ~v2_funct_1(D_287) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(A_290, B_289))) | ~v1_funct_2(D_287, A_290, B_289) | ~v1_funct_1(D_287))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.28/1.77  tff(c_2047, plain, (![D_291, B_292]: (k1_funct_1(k2_funct_1(D_291), k1_funct_1(D_291, '#skF_6'))='#skF_6' | k1_xboole_0=B_292 | ~v2_funct_1(D_291) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_292))) | ~v1_funct_2(D_291, '#skF_3', B_292) | ~v1_funct_1(D_291))), inference(resolution, [status(thm)], [c_1518, c_2025])).
% 4.28/1.77  tff(c_2058, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2047])).
% 4.28/1.77  tff(c_2064, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1514, c_2058])).
% 4.28/1.77  tff(c_2066, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2064])).
% 4.28/1.77  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.28/1.77  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.77  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_1516, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_48])).
% 4.28/1.77  tff(c_1589, plain, (![C_229, A_230, B_231]: (r2_hidden(C_229, A_230) | ~r2_hidden(C_229, B_231) | ~m1_subset_1(B_231, k1_zfmisc_1(A_230)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.28/1.77  tff(c_1596, plain, (![A_232]: (r2_hidden('#skF_5', A_232) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_232)))), inference(resolution, [status(thm)], [c_1516, c_1589])).
% 4.28/1.77  tff(c_1601, plain, (![B_9]: (r2_hidden('#skF_5', B_9) | ~r1_tarski('#skF_3', B_9))), inference(resolution, [status(thm)], [c_14, c_1596])).
% 4.28/1.77  tff(c_1618, plain, (![A_237, C_238, B_239]: (m1_subset_1(A_237, C_238) | ~m1_subset_1(B_239, k1_zfmisc_1(C_238)) | ~r2_hidden(A_237, B_239))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.28/1.77  tff(c_1630, plain, (![A_242, B_243, A_244]: (m1_subset_1(A_242, B_243) | ~r2_hidden(A_242, A_244) | ~r1_tarski(A_244, B_243))), inference(resolution, [status(thm)], [c_14, c_1618])).
% 4.28/1.77  tff(c_1659, plain, (![B_247, B_248]: (m1_subset_1('#skF_5', B_247) | ~r1_tarski(B_248, B_247) | ~r1_tarski('#skF_3', B_248))), inference(resolution, [status(thm)], [c_1601, c_1630])).
% 4.28/1.77  tff(c_1668, plain, (![A_3]: (m1_subset_1('#skF_5', A_3) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1659])).
% 4.28/1.77  tff(c_1669, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1668])).
% 4.28/1.77  tff(c_2074, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2066, c_1669])).
% 4.28/1.77  tff(c_2080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2074])).
% 4.28/1.77  tff(c_2082, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2064])).
% 4.28/1.77  tff(c_1513, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 4.28/1.77  tff(c_2081, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_2064])).
% 4.28/1.77  tff(c_44, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.28/1.77  tff(c_1530, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_44])).
% 4.28/1.77  tff(c_2149, plain, (![D_299, B_300]: (k1_funct_1(k2_funct_1(D_299), k1_funct_1(D_299, '#skF_5'))='#skF_5' | k1_xboole_0=B_300 | ~v2_funct_1(D_299) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_300))) | ~v1_funct_2(D_299, '#skF_3', B_300) | ~v1_funct_1(D_299))), inference(resolution, [status(thm)], [c_1516, c_2025])).
% 4.28/1.77  tff(c_2160, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2149])).
% 4.28/1.77  tff(c_2166, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1514, c_2081, c_1530, c_2160])).
% 4.28/1.77  tff(c_2168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2082, c_1513, c_2166])).
% 4.28/1.77  tff(c_2174, plain, (![A_301]: (m1_subset_1('#skF_5', A_301))), inference(splitRight, [status(thm)], [c_1668])).
% 4.28/1.77  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.77  tff(c_2188, plain, (![B_9]: (r1_tarski('#skF_5', B_9))), inference(resolution, [status(thm)], [c_2174, c_12])).
% 4.28/1.77  tff(c_2170, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1668])).
% 4.28/1.77  tff(c_1535, plain, (![B_218, A_219]: (B_218=A_219 | ~r1_tarski(B_218, A_219) | ~r1_tarski(A_219, B_218))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.77  tff(c_1547, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1535])).
% 4.28/1.77  tff(c_2198, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2170, c_1547])).
% 4.28/1.77  tff(c_2315, plain, (![A_312]: (A_312='#skF_3' | ~r1_tarski(A_312, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_2198, c_1547])).
% 4.28/1.77  tff(c_2333, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2188, c_2315])).
% 4.28/1.77  tff(c_2343, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2333, c_1513])).
% 4.28/1.77  tff(c_2205, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_8])).
% 4.28/1.77  tff(c_1644, plain, (![B_243]: (m1_subset_1('#skF_6', B_243) | ~r1_tarski('#skF_3', B_243))), inference(resolution, [status(thm)], [c_1518, c_1630])).
% 4.28/1.77  tff(c_2238, plain, (![B_304]: (m1_subset_1('#skF_6', B_304))), inference(demodulation, [status(thm), theory('equality')], [c_2205, c_1644])).
% 4.28/1.77  tff(c_2252, plain, (![B_9]: (r1_tarski('#skF_6', B_9))), inference(resolution, [status(thm)], [c_2238, c_12])).
% 4.28/1.77  tff(c_2332, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_2252, c_2315])).
% 4.28/1.77  tff(c_2352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2343, c_2332])).
% 4.28/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.77  
% 4.28/1.77  Inference rules
% 4.28/1.77  ----------------------
% 4.28/1.77  #Ref     : 5
% 4.28/1.77  #Sup     : 484
% 4.28/1.77  #Fact    : 0
% 4.28/1.77  #Define  : 0
% 4.28/1.77  #Split   : 23
% 4.28/1.77  #Chain   : 0
% 4.28/1.77  #Close   : 0
% 4.28/1.77  
% 4.28/1.77  Ordering : KBO
% 4.28/1.77  
% 4.28/1.77  Simplification rules
% 4.28/1.77  ----------------------
% 4.28/1.77  #Subsume      : 88
% 4.28/1.77  #Demod        : 294
% 4.28/1.77  #Tautology    : 169
% 4.28/1.77  #SimpNegUnit  : 14
% 4.28/1.77  #BackRed      : 32
% 4.28/1.77  
% 4.28/1.77  #Partial instantiations: 0
% 4.28/1.77  #Strategies tried      : 1
% 4.28/1.77  
% 4.28/1.77  Timing (in seconds)
% 4.28/1.77  ----------------------
% 4.28/1.77  Preprocessing        : 0.33
% 4.28/1.77  Parsing              : 0.17
% 4.28/1.77  CNF conversion       : 0.02
% 4.28/1.77  Main loop            : 0.65
% 4.28/1.77  Inferencing          : 0.23
% 4.28/1.78  Reduction            : 0.21
% 4.28/1.78  Demodulation         : 0.14
% 4.28/1.78  BG Simplification    : 0.03
% 4.28/1.78  Subsumption          : 0.12
% 4.28/1.78  Abstraction          : 0.03
% 4.28/1.78  MUC search           : 0.00
% 4.28/1.78  Cooper               : 0.00
% 4.28/1.78  Total                : 1.05
% 4.28/1.78  Index Insertion      : 0.00
% 4.28/1.78  Index Deletion       : 0.00
% 4.28/1.78  Index Matching       : 0.00
% 4.28/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
