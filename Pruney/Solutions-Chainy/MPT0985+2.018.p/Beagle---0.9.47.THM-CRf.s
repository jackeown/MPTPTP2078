%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:28 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  202 (1026 expanded)
%              Number of leaves         :   39 ( 349 expanded)
%              Depth                    :   12
%              Number of atoms          :  377 (2909 expanded)
%              Number of equality atoms :   90 ( 498 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_168,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_180,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_168])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_227,plain,(
    ! [C_74,B_75,A_76] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(B_75,A_76)))
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_241,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_227])).

tff(c_246,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_70,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_207,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_383,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_402,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_383])).

tff(c_624,plain,(
    ! [B_140,A_141,C_142] :
      ( k1_xboole_0 = B_140
      | k1_relset_1(A_141,B_140,C_142) = A_141
      | ~ v1_funct_2(C_142,A_141,B_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_630,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_624])).

tff(c_644,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_402,c_630])).

tff(c_648,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_36,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_140,plain,(
    ! [A_47] :
      ( v1_funct_1(k2_funct_1(A_47))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_139,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_143,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_139])).

tff(c_146,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_143])).

tff(c_148,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_151,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_148])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_151])).

tff(c_165,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_526,plain,(
    ! [B_131,A_132] :
      ( m1_subset_1(B_131,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_131),A_132)))
      | ~ r1_tarski(k2_relat_1(B_131),A_132)
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    ! [C_25,B_23,A_22] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_569,plain,(
    ! [B_135,A_136] :
      ( v1_xboole_0(B_135)
      | ~ v1_xboole_0(A_136)
      | ~ r1_tarski(k2_relat_1(B_135),A_136)
      | ~ v1_funct_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_526,c_42])).

tff(c_595,plain,(
    ! [B_138] :
      ( v1_xboole_0(B_138)
      | ~ v1_xboole_0(k2_relat_1(B_138))
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_207,c_569])).

tff(c_963,plain,(
    ! [A_170] :
      ( v1_xboole_0(k2_funct_1(A_170))
      | ~ v1_xboole_0(k1_relat_1(A_170))
      | ~ v1_funct_1(k2_funct_1(A_170))
      | ~ v1_relat_1(k2_funct_1(A_170))
      | ~ v2_funct_1(A_170)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_595])).

tff(c_128,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_979,plain,(
    ! [A_171] :
      ( k2_funct_1(A_171) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_171))
      | ~ v1_funct_1(k2_funct_1(A_171))
      | ~ v1_relat_1(k2_funct_1(A_171))
      | ~ v2_funct_1(A_171)
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_963,c_131])).

tff(c_982,plain,
    ( k2_funct_1('#skF_4') = k1_xboole_0
    | ~ v1_xboole_0('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_979])).

tff(c_990,plain,
    ( k2_funct_1('#skF_4') = k1_xboole_0
    | ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_165,c_982])).

tff(c_993,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_990])).

tff(c_996,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_993])).

tff(c_1000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_996])).

tff(c_1002,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_68,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_339,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_346,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_339])).

tff(c_359,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_346])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1109,plain,(
    ! [A_184,A_185] :
      ( m1_subset_1(k2_funct_1(A_184),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_184),A_185)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_184)),A_185)
      | ~ v1_funct_1(k2_funct_1(A_184))
      | ~ v1_relat_1(k2_funct_1(A_184))
      | ~ v2_funct_1(A_184)
      | ~ v1_funct_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_526])).

tff(c_1132,plain,(
    ! [A_185] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_185)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_185)
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1109])).

tff(c_1170,plain,(
    ! [A_187] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_187)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_1002,c_165,c_1132])).

tff(c_164,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_310,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_1202,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1170,c_310])).

tff(c_1209,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1202])).

tff(c_1212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_207,c_648,c_1209])).

tff(c_1213,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_16,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_609,plain,(
    ! [B_139] :
      ( m1_subset_1(B_139,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_139),k1_xboole_0)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_526])).

tff(c_612,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_609])).

tff(c_620,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_612])).

tff(c_623,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_620])).

tff(c_1216,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_623])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_1216])).

tff(c_1248,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_572,plain,(
    ! [A_136] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(A_136)
      | ~ r1_tarski('#skF_3',A_136)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_569])).

tff(c_584,plain,(
    ! [A_136] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(A_136)
      | ~ r1_tarski('#skF_3',A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_572])).

tff(c_588,plain,(
    ! [A_136] :
      ( ~ v1_xboole_0(A_136)
      | ~ r1_tarski('#skF_3',A_136) ) ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_1251,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1248,c_588])).

tff(c_1259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1251])).

tff(c_1260,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_1272,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1260,c_131])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1300,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1272,c_1272,c_26])).

tff(c_1322,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_359])).

tff(c_1334,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_246])).

tff(c_1341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_1334])).

tff(c_1343,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_1352,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1343,c_42])).

tff(c_1355,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_1457,plain,(
    ! [A_208,B_209,C_210] :
      ( k2_relset_1(A_208,B_209,C_210) = k2_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1467,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1457])).

tff(c_1481,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1467])).

tff(c_1342,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_1383,plain,(
    ! [A_194,B_195,C_196] :
      ( k1_relset_1(A_194,B_195,C_196) = k1_relat_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1404,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1343,c_1383])).

tff(c_1675,plain,(
    ! [B_247,C_248,A_249] :
      ( k1_xboole_0 = B_247
      | v1_funct_2(C_248,A_249,B_247)
      | k1_relset_1(A_249,B_247,C_248) != A_249
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1681,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1343,c_1675])).

tff(c_1697,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1404,c_1681])).

tff(c_1698,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1342,c_1697])).

tff(c_1704,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1698])).

tff(c_1707,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1704])).

tff(c_1710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_1481,c_1707])).

tff(c_1711,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1698])).

tff(c_1739,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_8])).

tff(c_1741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1355,c_1739])).

tff(c_1743,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_1755,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1743,c_131])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1772,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_1755,c_28])).

tff(c_1780,plain,(
    ! [A_250,B_251,C_252] :
      ( k2_relset_1(A_250,B_251,C_252) = k2_relat_1(C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1786,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1780])).

tff(c_1789,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1786])).

tff(c_1742,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( ~ v1_xboole_0(B_8)
      | B_8 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1827,plain,(
    ! [A_257] :
      ( A_257 = '#skF_2'
      | ~ v1_xboole_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_1743,c_12])).

tff(c_1834,plain,(
    k2_funct_1('#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1742,c_1827])).

tff(c_1848,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1834,c_38])).

tff(c_1861,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_1772,c_1789,c_1848])).

tff(c_1877,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1743])).

tff(c_1883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_1877])).

tff(c_1884,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_2679,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1884,c_131])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2712,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_10])).

tff(c_2710,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_2679,c_26])).

tff(c_2711,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_2679,c_28])).

tff(c_3089,plain,(
    ! [B_407,A_408] :
      ( v1_funct_2(B_407,k1_relat_1(B_407),A_408)
      | ~ r1_tarski(k2_relat_1(B_407),A_408)
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3098,plain,(
    ! [A_408] :
      ( v1_funct_2('#skF_4','#skF_4',A_408)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_408)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2711,c_3089])).

tff(c_3101,plain,(
    ! [A_408] : v1_funct_2('#skF_4','#skF_4',A_408) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_2712,c_2710,c_3098])).

tff(c_18,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2708,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_2679,c_18])).

tff(c_1885,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_2696,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1885,c_131])).

tff(c_2721,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_2696])).

tff(c_1898,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1884,c_131])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1926,plain,(
    ! [A_11] : m1_subset_1('#skF_4',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_20])).

tff(c_1930,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_1898,c_28])).

tff(c_2336,plain,(
    ! [B_325,A_326] :
      ( m1_subset_1(B_325,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_325),A_326)))
      | ~ r1_tarski(k2_relat_1(B_325),A_326)
      | ~ v1_funct_1(B_325)
      | ~ v1_relat_1(B_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2368,plain,(
    ! [B_327,A_328] :
      ( v1_xboole_0(B_327)
      | ~ v1_xboole_0(A_328)
      | ~ r1_tarski(k2_relat_1(B_327),A_328)
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327) ) ),
    inference(resolution,[status(thm)],[c_2336,c_42])).

tff(c_2382,plain,(
    ! [B_329] :
      ( v1_xboole_0(B_329)
      | ~ v1_xboole_0(k2_relat_1(B_329))
      | ~ v1_funct_1(B_329)
      | ~ v1_relat_1(B_329) ) ),
    inference(resolution,[status(thm)],[c_207,c_2368])).

tff(c_2613,plain,(
    ! [A_355] :
      ( v1_xboole_0(k2_funct_1(A_355))
      | ~ v1_xboole_0(k1_relat_1(A_355))
      | ~ v1_funct_1(k2_funct_1(A_355))
      | ~ v1_relat_1(k2_funct_1(A_355))
      | ~ v2_funct_1(A_355)
      | ~ v1_funct_1(A_355)
      | ~ v1_relat_1(A_355) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2382])).

tff(c_1899,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_1884,c_12])).

tff(c_2629,plain,(
    ! [A_356] :
      ( k2_funct_1(A_356) = '#skF_4'
      | ~ v1_xboole_0(k1_relat_1(A_356))
      | ~ v1_funct_1(k2_funct_1(A_356))
      | ~ v1_relat_1(k2_funct_1(A_356))
      | ~ v2_funct_1(A_356)
      | ~ v1_funct_1(A_356)
      | ~ v1_relat_1(A_356) ) ),
    inference(resolution,[status(thm)],[c_2613,c_1899])).

tff(c_2635,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_2629])).

tff(c_2637,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_70,c_165,c_1884,c_2635])).

tff(c_2638,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_2654,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2638])).

tff(c_2658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_76,c_2654])).

tff(c_2659,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_1927,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_1898,c_18])).

tff(c_1915,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1885,c_131])).

tff(c_1940,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_1915])).

tff(c_1886,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_1952,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1940,c_1886])).

tff(c_1985,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1952])).

tff(c_2661,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_1985])).

tff(c_2665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_2661])).

tff(c_2667,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2801,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2708,c_2721,c_2667])).

tff(c_240,plain,(
    ! [C_74] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_227])).

tff(c_245,plain,(
    ! [C_74] :
      ( v1_xboole_0(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_240])).

tff(c_2810,plain,(
    ! [C_364] :
      ( v1_xboole_0(C_364)
      | ~ m1_subset_1(C_364,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_245])).

tff(c_2818,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2801,c_2810])).

tff(c_2697,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_1885,c_12])).

tff(c_2756,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ v1_xboole_0(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_2697])).

tff(c_2832,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2818,c_2756])).

tff(c_2666,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2735,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2721,c_2666])).

tff(c_2840,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2735])).

tff(c_3104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3101,c_2840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.89  
% 4.83/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.89  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.83/1.89  
% 4.83/1.89  %Foreground sorts:
% 4.83/1.89  
% 4.83/1.89  
% 4.83/1.89  %Background operators:
% 4.83/1.89  
% 4.83/1.89  
% 4.83/1.89  %Foreground operators:
% 4.83/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.83/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.83/1.89  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.83/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.83/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.83/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.83/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.83/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.83/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.83/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.83/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.83/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.83/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.83/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/1.89  
% 4.83/1.92  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.83/1.92  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.83/1.92  tff(f_97, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.83/1.92  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.83/1.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.83/1.92  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.83/1.92  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.83/1.92  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.83/1.92  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.83/1.92  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.83/1.92  tff(f_43, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.83/1.92  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.83/1.92  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.83/1.92  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.83/1.92  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.83/1.92  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.83/1.92  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.92  tff(c_168, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/1.92  tff(c_180, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_168])).
% 4.83/1.92  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.92  tff(c_227, plain, (![C_74, B_75, A_76]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(B_75, A_76))) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.83/1.92  tff(c_241, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_227])).
% 4.83/1.92  tff(c_246, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_241])).
% 4.83/1.92  tff(c_70, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.92  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.83/1.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.83/1.92  tff(c_202, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.83/1.92  tff(c_207, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_202])).
% 4.83/1.92  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.92  tff(c_383, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.92  tff(c_402, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_383])).
% 4.83/1.92  tff(c_624, plain, (![B_140, A_141, C_142]: (k1_xboole_0=B_140 | k1_relset_1(A_141, B_140, C_142)=A_141 | ~v1_funct_2(C_142, A_141, B_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.92  tff(c_630, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_624])).
% 4.83/1.92  tff(c_644, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_402, c_630])).
% 4.83/1.92  tff(c_648, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_644])).
% 4.83/1.92  tff(c_36, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.83/1.92  tff(c_34, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.83/1.92  tff(c_140, plain, (![A_47]: (v1_funct_1(k2_funct_1(A_47)) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.83/1.92  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.92  tff(c_139, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 4.83/1.92  tff(c_143, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_140, c_139])).
% 4.83/1.92  tff(c_146, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_143])).
% 4.83/1.92  tff(c_148, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.83/1.92  tff(c_151, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_148])).
% 4.83/1.92  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_151])).
% 4.83/1.92  tff(c_165, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 4.83/1.92  tff(c_526, plain, (![B_131, A_132]: (m1_subset_1(B_131, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_131), A_132))) | ~r1_tarski(k2_relat_1(B_131), A_132) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.83/1.92  tff(c_42, plain, (![C_25, B_23, A_22]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.83/1.92  tff(c_569, plain, (![B_135, A_136]: (v1_xboole_0(B_135) | ~v1_xboole_0(A_136) | ~r1_tarski(k2_relat_1(B_135), A_136) | ~v1_funct_1(B_135) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_526, c_42])).
% 4.83/1.92  tff(c_595, plain, (![B_138]: (v1_xboole_0(B_138) | ~v1_xboole_0(k2_relat_1(B_138)) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_207, c_569])).
% 4.83/1.92  tff(c_963, plain, (![A_170]: (v1_xboole_0(k2_funct_1(A_170)) | ~v1_xboole_0(k1_relat_1(A_170)) | ~v1_funct_1(k2_funct_1(A_170)) | ~v1_relat_1(k2_funct_1(A_170)) | ~v2_funct_1(A_170) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(superposition, [status(thm), theory('equality')], [c_36, c_595])).
% 4.83/1.92  tff(c_128, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | B_43=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.92  tff(c_131, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_8, c_128])).
% 4.83/1.92  tff(c_979, plain, (![A_171]: (k2_funct_1(A_171)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_171)) | ~v1_funct_1(k2_funct_1(A_171)) | ~v1_relat_1(k2_funct_1(A_171)) | ~v2_funct_1(A_171) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_963, c_131])).
% 4.83/1.92  tff(c_982, plain, (k2_funct_1('#skF_4')=k1_xboole_0 | ~v1_xboole_0('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_648, c_979])).
% 4.83/1.92  tff(c_990, plain, (k2_funct_1('#skF_4')=k1_xboole_0 | ~v1_xboole_0('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_165, c_982])).
% 4.83/1.92  tff(c_993, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_990])).
% 4.83/1.92  tff(c_996, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_993])).
% 4.83/1.92  tff(c_1000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_996])).
% 4.83/1.92  tff(c_1002, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_990])).
% 4.83/1.92  tff(c_68, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.92  tff(c_339, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.83/1.92  tff(c_346, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_339])).
% 4.83/1.92  tff(c_359, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_346])).
% 4.83/1.92  tff(c_38, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.83/1.92  tff(c_1109, plain, (![A_184, A_185]: (m1_subset_1(k2_funct_1(A_184), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_184), A_185))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_184)), A_185) | ~v1_funct_1(k2_funct_1(A_184)) | ~v1_relat_1(k2_funct_1(A_184)) | ~v2_funct_1(A_184) | ~v1_funct_1(A_184) | ~v1_relat_1(A_184))), inference(superposition, [status(thm), theory('equality')], [c_38, c_526])).
% 4.83/1.92  tff(c_1132, plain, (![A_185]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_185))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_185) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_1109])).
% 4.83/1.92  tff(c_1170, plain, (![A_187]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_187))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), A_187))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_1002, c_165, c_1132])).
% 4.83/1.92  tff(c_164, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 4.83/1.92  tff(c_310, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_164])).
% 4.83/1.92  tff(c_1202, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_4')), '#skF_2')), inference(resolution, [status(thm)], [c_1170, c_310])).
% 4.83/1.92  tff(c_1209, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1202])).
% 4.83/1.92  tff(c_1212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_207, c_648, c_1209])).
% 4.83/1.92  tff(c_1213, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_644])).
% 4.83/1.92  tff(c_16, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.92  tff(c_609, plain, (![B_139]: (m1_subset_1(B_139, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_139), k1_xboole_0) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(superposition, [status(thm), theory('equality')], [c_16, c_526])).
% 4.83/1.92  tff(c_612, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_359, c_609])).
% 4.83/1.92  tff(c_620, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_612])).
% 4.83/1.92  tff(c_623, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_620])).
% 4.83/1.92  tff(c_1216, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_623])).
% 4.83/1.92  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_1216])).
% 4.83/1.92  tff(c_1248, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_620])).
% 4.83/1.92  tff(c_572, plain, (![A_136]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(A_136) | ~r1_tarski('#skF_3', A_136) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_569])).
% 4.83/1.92  tff(c_584, plain, (![A_136]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(A_136) | ~r1_tarski('#skF_3', A_136))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_572])).
% 4.83/1.92  tff(c_588, plain, (![A_136]: (~v1_xboole_0(A_136) | ~r1_tarski('#skF_3', A_136))), inference(splitLeft, [status(thm)], [c_584])).
% 4.83/1.92  tff(c_1251, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1248, c_588])).
% 4.83/1.92  tff(c_1259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1251])).
% 4.83/1.92  tff(c_1260, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_584])).
% 4.83/1.92  tff(c_1272, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1260, c_131])).
% 4.83/1.92  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.83/1.92  tff(c_1300, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1272, c_1272, c_26])).
% 4.83/1.92  tff(c_1322, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_359])).
% 4.83/1.92  tff(c_1334, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1322, c_246])).
% 4.83/1.92  tff(c_1341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1260, c_1334])).
% 4.83/1.92  tff(c_1343, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_164])).
% 4.83/1.92  tff(c_1352, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1343, c_42])).
% 4.83/1.92  tff(c_1355, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1352])).
% 4.83/1.92  tff(c_1457, plain, (![A_208, B_209, C_210]: (k2_relset_1(A_208, B_209, C_210)=k2_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.83/1.92  tff(c_1467, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1457])).
% 4.83/1.92  tff(c_1481, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1467])).
% 4.83/1.92  tff(c_1342, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_164])).
% 4.83/1.92  tff(c_1383, plain, (![A_194, B_195, C_196]: (k1_relset_1(A_194, B_195, C_196)=k1_relat_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.92  tff(c_1404, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1343, c_1383])).
% 4.83/1.92  tff(c_1675, plain, (![B_247, C_248, A_249]: (k1_xboole_0=B_247 | v1_funct_2(C_248, A_249, B_247) | k1_relset_1(A_249, B_247, C_248)!=A_249 | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.83/1.92  tff(c_1681, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_1343, c_1675])).
% 4.83/1.92  tff(c_1697, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1404, c_1681])).
% 4.83/1.92  tff(c_1698, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1342, c_1697])).
% 4.83/1.92  tff(c_1704, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_1698])).
% 4.83/1.92  tff(c_1707, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_1704])).
% 4.83/1.92  tff(c_1710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_1481, c_1707])).
% 4.83/1.92  tff(c_1711, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1698])).
% 4.83/1.92  tff(c_1739, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_8])).
% 4.83/1.92  tff(c_1741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1355, c_1739])).
% 4.83/1.92  tff(c_1743, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1352])).
% 4.83/1.92  tff(c_1755, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1743, c_131])).
% 4.83/1.92  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.83/1.92  tff(c_1772, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_1755, c_28])).
% 4.83/1.92  tff(c_1780, plain, (![A_250, B_251, C_252]: (k2_relset_1(A_250, B_251, C_252)=k2_relat_1(C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.83/1.92  tff(c_1786, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1780])).
% 4.83/1.92  tff(c_1789, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1786])).
% 4.83/1.92  tff(c_1742, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1352])).
% 4.83/1.92  tff(c_12, plain, (![B_8, A_7]: (~v1_xboole_0(B_8) | B_8=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.92  tff(c_1827, plain, (![A_257]: (A_257='#skF_2' | ~v1_xboole_0(A_257))), inference(resolution, [status(thm)], [c_1743, c_12])).
% 4.83/1.92  tff(c_1834, plain, (k2_funct_1('#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_1742, c_1827])).
% 4.83/1.92  tff(c_1848, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1834, c_38])).
% 4.83/1.92  tff(c_1861, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_1772, c_1789, c_1848])).
% 4.83/1.92  tff(c_1877, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1743])).
% 4.83/1.92  tff(c_1883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_1877])).
% 4.83/1.92  tff(c_1884, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_241])).
% 4.83/1.92  tff(c_2679, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1884, c_131])).
% 4.83/1.92  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.83/1.92  tff(c_2712, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_10])).
% 4.83/1.92  tff(c_2710, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_2679, c_26])).
% 4.83/1.92  tff(c_2711, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_2679, c_28])).
% 4.83/1.92  tff(c_3089, plain, (![B_407, A_408]: (v1_funct_2(B_407, k1_relat_1(B_407), A_408) | ~r1_tarski(k2_relat_1(B_407), A_408) | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.83/1.92  tff(c_3098, plain, (![A_408]: (v1_funct_2('#skF_4', '#skF_4', A_408) | ~r1_tarski(k2_relat_1('#skF_4'), A_408) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2711, c_3089])).
% 4.83/1.92  tff(c_3101, plain, (![A_408]: (v1_funct_2('#skF_4', '#skF_4', A_408))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_2712, c_2710, c_3098])).
% 4.83/1.92  tff(c_18, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/1.92  tff(c_2708, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_2679, c_18])).
% 4.83/1.92  tff(c_1885, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_241])).
% 4.83/1.92  tff(c_2696, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1885, c_131])).
% 4.83/1.92  tff(c_2721, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_2696])).
% 4.83/1.92  tff(c_1898, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1884, c_131])).
% 4.83/1.92  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/1.92  tff(c_1926, plain, (![A_11]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_20])).
% 4.83/1.92  tff(c_1930, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_1898, c_28])).
% 4.83/1.92  tff(c_2336, plain, (![B_325, A_326]: (m1_subset_1(B_325, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_325), A_326))) | ~r1_tarski(k2_relat_1(B_325), A_326) | ~v1_funct_1(B_325) | ~v1_relat_1(B_325))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.83/1.92  tff(c_2368, plain, (![B_327, A_328]: (v1_xboole_0(B_327) | ~v1_xboole_0(A_328) | ~r1_tarski(k2_relat_1(B_327), A_328) | ~v1_funct_1(B_327) | ~v1_relat_1(B_327))), inference(resolution, [status(thm)], [c_2336, c_42])).
% 4.83/1.92  tff(c_2382, plain, (![B_329]: (v1_xboole_0(B_329) | ~v1_xboole_0(k2_relat_1(B_329)) | ~v1_funct_1(B_329) | ~v1_relat_1(B_329))), inference(resolution, [status(thm)], [c_207, c_2368])).
% 4.83/1.92  tff(c_2613, plain, (![A_355]: (v1_xboole_0(k2_funct_1(A_355)) | ~v1_xboole_0(k1_relat_1(A_355)) | ~v1_funct_1(k2_funct_1(A_355)) | ~v1_relat_1(k2_funct_1(A_355)) | ~v2_funct_1(A_355) | ~v1_funct_1(A_355) | ~v1_relat_1(A_355))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2382])).
% 4.83/1.92  tff(c_1899, plain, (![A_7]: (A_7='#skF_4' | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_1884, c_12])).
% 4.83/1.92  tff(c_2629, plain, (![A_356]: (k2_funct_1(A_356)='#skF_4' | ~v1_xboole_0(k1_relat_1(A_356)) | ~v1_funct_1(k2_funct_1(A_356)) | ~v1_relat_1(k2_funct_1(A_356)) | ~v2_funct_1(A_356) | ~v1_funct_1(A_356) | ~v1_relat_1(A_356))), inference(resolution, [status(thm)], [c_2613, c_1899])).
% 4.83/1.92  tff(c_2635, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1930, c_2629])).
% 4.83/1.92  tff(c_2637, plain, (k2_funct_1('#skF_4')='#skF_4' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_70, c_165, c_1884, c_2635])).
% 4.83/1.92  tff(c_2638, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2637])).
% 4.83/1.92  tff(c_2654, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_2638])).
% 4.83/1.92  tff(c_2658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_76, c_2654])).
% 4.83/1.92  tff(c_2659, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2637])).
% 4.83/1.92  tff(c_1927, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_1898, c_18])).
% 4.83/1.92  tff(c_1915, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1885, c_131])).
% 4.83/1.92  tff(c_1940, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1898, c_1915])).
% 4.83/1.92  tff(c_1886, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_164])).
% 4.83/1.92  tff(c_1952, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1940, c_1886])).
% 4.83/1.92  tff(c_1985, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1952])).
% 4.83/1.92  tff(c_2661, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2659, c_1985])).
% 4.83/1.92  tff(c_2665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1926, c_2661])).
% 4.83/1.92  tff(c_2667, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_164])).
% 4.83/1.92  tff(c_2801, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2708, c_2721, c_2667])).
% 4.83/1.92  tff(c_240, plain, (![C_74]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_227])).
% 4.83/1.92  tff(c_245, plain, (![C_74]: (v1_xboole_0(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_240])).
% 4.83/1.92  tff(c_2810, plain, (![C_364]: (v1_xboole_0(C_364) | ~m1_subset_1(C_364, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_245])).
% 4.83/1.92  tff(c_2818, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2801, c_2810])).
% 4.83/1.92  tff(c_2697, plain, (![A_7]: (A_7='#skF_3' | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_1885, c_12])).
% 4.83/1.92  tff(c_2756, plain, (![A_7]: (A_7='#skF_4' | ~v1_xboole_0(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2721, c_2697])).
% 4.83/1.92  tff(c_2832, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2818, c_2756])).
% 4.83/1.92  tff(c_2666, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_164])).
% 4.83/1.92  tff(c_2735, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2721, c_2666])).
% 4.83/1.92  tff(c_2840, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2735])).
% 4.83/1.92  tff(c_3104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3101, c_2840])).
% 4.83/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.92  
% 4.83/1.92  Inference rules
% 4.83/1.92  ----------------------
% 4.83/1.92  #Ref     : 0
% 4.83/1.92  #Sup     : 630
% 4.83/1.92  #Fact    : 0
% 4.83/1.92  #Define  : 0
% 4.83/1.92  #Split   : 16
% 4.83/1.92  #Chain   : 0
% 4.83/1.92  #Close   : 0
% 4.83/1.92  
% 4.83/1.92  Ordering : KBO
% 4.83/1.92  
% 4.83/1.92  Simplification rules
% 4.83/1.92  ----------------------
% 4.83/1.92  #Subsume      : 131
% 4.83/1.92  #Demod        : 831
% 4.83/1.92  #Tautology    : 300
% 4.83/1.92  #SimpNegUnit  : 4
% 4.83/1.92  #BackRed      : 171
% 4.83/1.92  
% 4.83/1.92  #Partial instantiations: 0
% 4.83/1.92  #Strategies tried      : 1
% 4.83/1.92  
% 4.83/1.92  Timing (in seconds)
% 4.83/1.92  ----------------------
% 5.16/1.92  Preprocessing        : 0.35
% 5.16/1.92  Parsing              : 0.19
% 5.16/1.92  CNF conversion       : 0.02
% 5.16/1.92  Main loop            : 0.77
% 5.16/1.92  Inferencing          : 0.28
% 5.16/1.92  Reduction            : 0.25
% 5.16/1.92  Demodulation         : 0.18
% 5.16/1.92  BG Simplification    : 0.03
% 5.16/1.92  Subsumption          : 0.14
% 5.16/1.92  Abstraction          : 0.03
% 5.16/1.92  MUC search           : 0.00
% 5.16/1.92  Cooper               : 0.00
% 5.16/1.92  Total                : 1.18
% 5.16/1.92  Index Insertion      : 0.00
% 5.16/1.92  Index Deletion       : 0.00
% 5.16/1.92  Index Matching       : 0.00
% 5.16/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
