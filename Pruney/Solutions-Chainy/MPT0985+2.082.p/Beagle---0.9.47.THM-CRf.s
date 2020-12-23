%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:39 EST 2020

% Result     : Theorem 14.20s
% Output     : CNFRefutation 14.95s
% Verified   : 
% Statistics : Number of formulae       :  817 (17268 expanded)
%              Number of leaves         :   35 (5282 expanded)
%              Depth                    :   23
%              Number of atoms          : 1570 (46223 expanded)
%              Number of equality atoms :  468 (14340 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_130,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_27978,plain,(
    ! [C_1756,A_1757,B_1758] :
      ( v1_relat_1(C_1756)
      | ~ m1_subset_1(C_1756,k1_zfmisc_1(k2_zfmisc_1(A_1757,B_1758))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_27995,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_27978])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32858,plain,(
    ! [A_2147,B_2148,C_2149] :
      ( k2_relset_1(A_2147,B_2148,C_2149) = k2_relat_1(C_2149)
      | ~ m1_subset_1(C_2149,k1_zfmisc_1(k2_zfmisc_1(A_2147,B_2148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32868,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_32858])).

tff(c_32877,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32868])).

tff(c_28,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_166])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_463,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_478,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_463])).

tff(c_912,plain,(
    ! [B_162,A_163,C_164] :
      ( k1_xboole_0 = B_162
      | k1_relset_1(A_163,B_162,C_164) = A_163
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_922,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_912])).

tff(c_933,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_478,c_922])).

tff(c_935,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_26,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_409,plain,(
    ! [A_94] :
      ( k2_relat_1(k2_funct_1(A_94)) = k1_relat_1(A_94)
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_304,plain,(
    ! [B_76,A_77] :
      ( v5_relat_1(B_76,A_77)
      | ~ r1_tarski(k2_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_313,plain,(
    ! [B_76] :
      ( v5_relat_1(B_76,k2_relat_1(B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_304])).

tff(c_3080,plain,(
    ! [A_293] :
      ( v5_relat_1(k2_funct_1(A_293),k1_relat_1(A_293))
      | ~ v1_relat_1(k2_funct_1(A_293))
      | ~ v2_funct_1(A_293)
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_313])).

tff(c_3083,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_3080])).

tff(c_3088,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_3083])).

tff(c_3089,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3088])).

tff(c_3092,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_3089])).

tff(c_3096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_3092])).

tff(c_3098,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3088])).

tff(c_103,plain,(
    ! [A_33] :
      ( v1_funct_1(k2_funct_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_102,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_106,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_102])).

tff(c_109,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_106])).

tff(c_131,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_131])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_138])).

tff(c_149,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_553,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_560,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_553])).

tff(c_569,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_560])).

tff(c_723,plain,(
    ! [B_138,A_139] :
      ( m1_subset_1(B_138,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_138),A_139)))
      | ~ r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5261,plain,(
    ! [A_346,A_347] :
      ( m1_subset_1(k2_funct_1(A_346),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_346),A_347)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_346)),A_347)
      | ~ v1_funct_1(k2_funct_1(A_346))
      | ~ v1_relat_1(k2_funct_1(A_346))
      | ~ v2_funct_1(A_346)
      | ~ v1_funct_1(A_346)
      | ~ v1_relat_1(A_346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_723])).

tff(c_5294,plain,(
    ! [A_347] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_347)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_347)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_5261])).

tff(c_5383,plain,(
    ! [A_350] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_350)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_350) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_3098,c_149,c_5294])).

tff(c_148,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_150,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_5423,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5383,c_150])).

tff(c_5427,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_5423])).

tff(c_5433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_6,c_935,c_5427])).

tff(c_5434,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_18,plain,(
    ! [B_8,A_7] :
      ( v5_relat_1(B_8,A_7)
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_579,plain,(
    ! [A_7] :
      ( v5_relat_1('#skF_3',A_7)
      | ~ r1_tarski('#skF_2',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_18])).

tff(c_613,plain,(
    ! [A_122] :
      ( v5_relat_1('#skF_3',A_122)
      | ~ r1_tarski('#skF_2',A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_579])).

tff(c_282,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k2_relat_1(B_72),A_73)
      | ~ v5_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [C_49] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_185,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_180])).

tff(c_300,plain,(
    ! [B_72] :
      ( v1_relat_1(k2_relat_1(B_72))
      | ~ v5_relat_1(B_72,k1_xboole_0)
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_282,c_185])).

tff(c_582,plain,
    ( v1_relat_1('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_300])).

tff(c_595,plain,
    ( v1_relat_1('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_582])).

tff(c_600,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_621,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_613,c_600])).

tff(c_5448,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5434,c_621])).

tff(c_5477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5448])).

tff(c_5479,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_585,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_2',A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_20])).

tff(c_5496,plain,(
    ! [A_354] :
      ( r1_tarski('#skF_2',A_354)
      | ~ v5_relat_1('#skF_3',A_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_585])).

tff(c_5515,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5479,c_5496])).

tff(c_5848,plain,(
    ! [B_397,A_398,C_399] :
      ( k1_xboole_0 = B_397
      | k1_relset_1(A_398,B_397,C_399) = A_398
      | ~ v1_funct_2(C_399,A_398,B_397)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_398,B_397))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5858,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_5848])).

tff(c_5869,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_478,c_5858])).

tff(c_5871,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5869])).

tff(c_54,plain,(
    ! [B_27,A_26] :
      ( v1_funct_2(B_27,k1_relat_1(B_27),A_26)
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5879,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_3','#skF_1',A_26)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5871,c_54])).

tff(c_5891,plain,(
    ! [A_400] :
      ( v1_funct_2('#skF_3','#skF_1',A_400)
      | ~ r1_tarski('#skF_2',A_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_569,c_5879])).

tff(c_42,plain,(
    ! [C_25,A_23] :
      ( k1_xboole_0 = C_25
      | ~ v1_funct_2(C_25,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_72,plain,(
    ! [C_25,A_23] :
      ( k1_xboole_0 = C_25
      | ~ v1_funct_2(C_25,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_5894,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5891,c_72])).

tff(c_5897,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5515,c_5894])).

tff(c_5898,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_5897])).

tff(c_52,plain,(
    ! [B_27,A_26] :
      ( m1_subset_1(B_27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_27),A_26)))
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5876,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_26)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5871,c_52])).

tff(c_5903,plain,(
    ! [A_401] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_401)))
      | ~ r1_tarski('#skF_2',A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_569,c_5876])).

tff(c_5928,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_5903])).

tff(c_5941,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5515,c_5928])).

tff(c_5943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5898,c_5941])).

tff(c_5944,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5897])).

tff(c_5946,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5944])).

tff(c_235,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_251,plain,(
    ! [C_63,B_64] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_235])).

tff(c_255,plain,(
    ! [A_5,B_64] :
      ( v5_relat_1(A_5,B_64)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_251])).

tff(c_178,plain,(
    ! [A_5,A_47,B_48] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_439,plain,(
    ! [B_97,A_98,B_99] :
      ( v1_relat_1(k2_relat_1(B_97))
      | ~ v5_relat_1(B_97,k2_zfmisc_1(A_98,B_99))
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_282,c_178])).

tff(c_462,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_255,c_439])).

tff(c_573,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_462])).

tff(c_589,plain,
    ( v1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_573])).

tff(c_599,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_5993,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5946,c_599])).

tff(c_6023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5993])).

tff(c_6024,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5944])).

tff(c_6049,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6024,c_599])).

tff(c_5945,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_5897])).

tff(c_6151,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6024,c_5945])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6154,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_6151,c_14])).

tff(c_6158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6049,c_6154])).

tff(c_6159,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5869])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5530,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_5515,c_2])).

tff(c_5533,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5530])).

tff(c_6178,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6159,c_5533])).

tff(c_6209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6178])).

tff(c_6210,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5530])).

tff(c_6215,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6210,c_599])).

tff(c_6238,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6210,c_6210,c_10])).

tff(c_153,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_6271,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6238,c_161])).

tff(c_6274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6215,c_6271])).

tff(c_6276,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_6306,plain,(
    ! [A_418] :
      ( r1_tarski('#skF_2',A_418)
      | ~ v5_relat_1('#skF_3',A_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_585])).

tff(c_6317,plain,(
    ! [B_64] :
      ( r1_tarski('#skF_2',B_64)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_255,c_6306])).

tff(c_6327,plain,(
    ! [B_64] : r1_tarski('#skF_2',B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6276,c_6317])).

tff(c_7096,plain,(
    ! [B_480,A_481,C_482] :
      ( k1_xboole_0 = B_480
      | k1_relset_1(A_481,B_480,C_482) = A_481
      | ~ v1_funct_2(C_482,A_481,B_480)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_481,B_480))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_7106,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_7096])).

tff(c_7117,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_478,c_7106])).

tff(c_7119,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7117])).

tff(c_8548,plain,(
    ! [A_567,A_568] :
      ( v5_relat_1(k2_funct_1(A_567),A_568)
      | ~ r1_tarski(k1_relat_1(A_567),A_568)
      | ~ v1_relat_1(k2_funct_1(A_567))
      | ~ v2_funct_1(A_567)
      | ~ v1_funct_1(A_567)
      | ~ v1_relat_1(A_567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_18])).

tff(c_6333,plain,(
    ! [B_419] : r1_tarski('#skF_2',B_419) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6276,c_6317])).

tff(c_6390,plain,(
    ! [B_425] :
      ( B_425 = '#skF_2'
      | ~ r1_tarski(B_425,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6333,c_2])).

tff(c_6405,plain,(
    ! [B_8] :
      ( k2_relat_1(B_8) = '#skF_2'
      | ~ v5_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_6390])).

tff(c_8651,plain,(
    ! [A_575] :
      ( k2_relat_1(k2_funct_1(A_575)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1(A_575),'#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_575))
      | ~ v2_funct_1(A_575)
      | ~ v1_funct_1(A_575)
      | ~ v1_relat_1(A_575) ) ),
    inference(resolution,[status(thm)],[c_8548,c_6405])).

tff(c_8654,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7119,c_8651])).

tff(c_8659,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_8654])).

tff(c_8951,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8659])).

tff(c_8954,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_8951])).

tff(c_8958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_8954])).

tff(c_8960,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8659])).

tff(c_418,plain,(
    ! [A_94,A_7] :
      ( v5_relat_1(k2_funct_1(A_94),A_7)
      | ~ r1_tarski(k1_relat_1(A_94),A_7)
      | ~ v1_relat_1(k2_funct_1(A_94))
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_18])).

tff(c_7126,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_26)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7119,c_52])).

tff(c_7170,plain,(
    ! [A_486] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_486))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_6327,c_569,c_7126])).

tff(c_7197,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7170])).

tff(c_7129,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_3','#skF_1',A_26)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7119,c_54])).

tff(c_7138,plain,(
    ! [A_483] : v1_funct_2('#skF_3','#skF_1',A_483) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_6327,c_569,c_7129])).

tff(c_7142,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_7138,c_72])).

tff(c_7363,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7197,c_7142])).

tff(c_7364,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7363])).

tff(c_6762,plain,(
    ! [B_443,A_444] :
      ( m1_subset_1(B_443,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_443),A_444)))
      | ~ r1_tarski(k2_relat_1(B_443),A_444)
      | ~ v1_funct_1(B_443)
      | ~ v1_relat_1(B_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6787,plain,(
    ! [B_443] :
      ( m1_subset_1(B_443,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_443),k1_xboole_0)
      | ~ v1_funct_1(B_443)
      | ~ v1_relat_1(B_443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6762])).

tff(c_7439,plain,(
    ! [B_495] :
      ( m1_subset_1(B_495,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(B_495),'#skF_1')
      | ~ v1_funct_1(B_495)
      | ~ v1_relat_1(B_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_7364,c_6787])).

tff(c_9297,plain,(
    ! [B_609] :
      ( m1_subset_1(B_609,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(B_609)
      | ~ v5_relat_1(B_609,'#skF_1')
      | ~ v1_relat_1(B_609) ) ),
    inference(resolution,[status(thm)],[c_20,c_7439])).

tff(c_7408,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_7364,c_10])).

tff(c_7504,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7408,c_150])).

tff(c_9315,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9297,c_7504])).

tff(c_9328,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8960,c_149,c_9315])).

tff(c_9363,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_418,c_9328])).

tff(c_9370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_8960,c_6,c_7119,c_9363])).

tff(c_9371,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7363])).

tff(c_6285,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6276,c_2])).

tff(c_6297,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6285])).

tff(c_9392,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9371,c_6297])).

tff(c_9421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9392])).

tff(c_9422,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7117])).

tff(c_9442,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9422,c_6297])).

tff(c_9472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6327,c_9442])).

tff(c_9473,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6285])).

tff(c_9499,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9473,c_9473,c_10])).

tff(c_50,plain,(
    ! [B_24,A_23,C_25] :
      ( k1_xboole_0 = B_24
      | k1_relset_1(A_23,B_24,C_25) = A_23
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9936,plain,(
    ! [B_646,A_647,C_648] :
      ( B_646 = '#skF_3'
      | k1_relset_1(A_647,B_646,C_648) = A_647
      | ~ v1_funct_2(C_648,A_647,B_646)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(k2_zfmisc_1(A_647,B_646))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9473,c_50])).

tff(c_9952,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_9936])).

tff(c_9958,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_478,c_9952])).

tff(c_9959,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9958])).

tff(c_12351,plain,(
    ! [A_783,A_784] :
      ( v5_relat_1(k2_funct_1(A_783),A_784)
      | ~ r1_tarski(k1_relat_1(A_783),A_784)
      | ~ v1_relat_1(k2_funct_1(A_783))
      | ~ v2_funct_1(A_783)
      | ~ v1_funct_1(A_783)
      | ~ v1_relat_1(A_783) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_18])).

tff(c_258,plain,(
    ! [A_67,B_68,A_69] :
      ( v5_relat_1(A_67,B_68)
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_69,B_68)) ) ),
    inference(resolution,[status(thm)],[c_16,c_235])).

tff(c_275,plain,(
    ! [A_70,B_71] : v5_relat_1(k2_zfmisc_1(A_70,B_71),B_71) ),
    inference(resolution,[status(thm)],[c_6,c_258])).

tff(c_278,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_275])).

tff(c_9491,plain,(
    ! [B_4] : v5_relat_1('#skF_3',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9473,c_278])).

tff(c_597,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_2',A_7)
      | ~ v5_relat_1('#skF_3',A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_585])).

tff(c_9654,plain,(
    ! [A_620] : r1_tarski('#skF_2',A_620) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9491,c_597])).

tff(c_9689,plain,(
    ! [A_623] :
      ( A_623 = '#skF_2'
      | ~ r1_tarski(A_623,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_9654,c_2])).

tff(c_9704,plain,(
    ! [B_8] :
      ( k2_relat_1(B_8) = '#skF_2'
      | ~ v5_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_9689])).

tff(c_12449,plain,(
    ! [A_786] :
      ( k2_relat_1(k2_funct_1(A_786)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1(A_786),'#skF_2')
      | ~ v1_relat_1(k2_funct_1(A_786))
      | ~ v2_funct_1(A_786)
      | ~ v1_funct_1(A_786)
      | ~ v1_relat_1(A_786) ) ),
    inference(resolution,[status(thm)],[c_12351,c_9704])).

tff(c_12452,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9959,c_12449])).

tff(c_12457,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_12452])).

tff(c_12458,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12457])).

tff(c_12461,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_12458])).

tff(c_12465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_12461])).

tff(c_12467,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12457])).

tff(c_9732,plain,(
    ! [B_630,A_631] :
      ( m1_subset_1(B_630,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_630),A_631)))
      | ~ r1_tarski(k2_relat_1(B_630),A_631)
      | ~ v1_funct_1(B_630)
      | ~ v1_relat_1(B_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12871,plain,(
    ! [A_808,A_809] :
      ( m1_subset_1(k2_funct_1(A_808),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_808),A_809)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_808)),A_809)
      | ~ v1_funct_1(k2_funct_1(A_808))
      | ~ v1_relat_1(k2_funct_1(A_808))
      | ~ v2_funct_1(A_808)
      | ~ v1_funct_1(A_808)
      | ~ v1_relat_1(A_808) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_9732])).

tff(c_12923,plain,(
    ! [A_809] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_809)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_809)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_12871])).

tff(c_12957,plain,(
    ! [A_812] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_812)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_12467,c_149,c_12923])).

tff(c_12997,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12957,c_150])).

tff(c_13001,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_12997])).

tff(c_13007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_6,c_9959,c_13001])).

tff(c_13008,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9958])).

tff(c_225,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_225])).

tff(c_256,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_13022,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13008,c_256])).

tff(c_13037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9499,c_13022])).

tff(c_13038,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13049,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_8])).

tff(c_13104,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13049])).

tff(c_13041,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13038,c_64])).

tff(c_13464,plain,(
    ! [A_873,B_874,C_875] :
      ( k1_relset_1(A_873,B_874,C_875) = k1_relat_1(C_875)
      | ~ m1_subset_1(C_875,k1_zfmisc_1(k2_zfmisc_1(A_873,B_874))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13498,plain,(
    ! [C_878] :
      ( k1_relset_1('#skF_1','#skF_2',C_878) = k1_relat_1(C_878)
      | ~ m1_subset_1(C_878,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_13464])).

tff(c_13506,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13041,c_13498])).

tff(c_14147,plain,(
    ! [B_944,C_945,A_946] :
      ( k1_xboole_0 = B_944
      | v1_funct_2(C_945,A_946,B_944)
      | k1_relset_1(A_946,B_944,C_945) != A_946
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(A_946,B_944))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14153,plain,(
    ! [C_945] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_945,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_945) != '#skF_1'
      | ~ m1_subset_1(C_945,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_14147])).

tff(c_14241,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14153])).

tff(c_13550,plain,(
    ! [A_884,B_885,C_886] :
      ( k2_relset_1(A_884,B_885,C_886) = k2_relat_1(C_886)
      | ~ m1_subset_1(C_886,k1_zfmisc_1(k2_zfmisc_1(A_884,B_885))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_13587,plain,(
    ! [C_890] :
      ( k2_relset_1('#skF_1','#skF_2',C_890) = k2_relat_1(C_890)
      | ~ m1_subset_1(C_890,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_13550])).

tff(c_13590,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13041,c_13587])).

tff(c_13596,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_13590])).

tff(c_13622,plain,(
    ! [A_7] :
      ( v5_relat_1('#skF_3',A_7)
      | ~ r1_tarski('#skF_2',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_18])).

tff(c_13673,plain,(
    ! [A_894] :
      ( v5_relat_1('#skF_3',A_894)
      | ~ r1_tarski('#skF_2',A_894) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_13622])).

tff(c_13073,plain,(
    ! [B_814,A_815] :
      ( r1_tarski(k2_relat_1(B_814),A_815)
      | ~ v5_relat_1(B_814,A_815)
      | ~ v1_relat_1(B_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13091,plain,(
    ! [B_814] :
      ( v1_relat_1(k2_relat_1(B_814))
      | ~ v5_relat_1(B_814,k1_xboole_0)
      | ~ v1_relat_1(B_814) ) ),
    inference(resolution,[status(thm)],[c_13073,c_185])).

tff(c_13613,plain,
    ( v1_relat_1('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_13091])).

tff(c_13637,plain,
    ( v1_relat_1('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_13613])).

tff(c_13648,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_13637])).

tff(c_13688,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13673,c_13648])).

tff(c_14267,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14241,c_13688])).

tff(c_14308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14267])).

tff(c_14310,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14153])).

tff(c_14219,plain,(
    ! [B_960,A_961,C_962] :
      ( k1_xboole_0 = B_960
      | k1_relset_1(A_961,B_960,C_962) = A_961
      | ~ v1_funct_2(C_962,A_961,B_960)
      | ~ m1_subset_1(C_962,k1_zfmisc_1(k2_zfmisc_1(A_961,B_960))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14225,plain,(
    ! [C_962] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_962) = '#skF_1'
      | ~ v1_funct_2(C_962,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_962,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_14219])).

tff(c_14421,plain,(
    ! [C_981] :
      ( k1_relset_1('#skF_1','#skF_2',C_981) = '#skF_1'
      | ~ v1_funct_2(C_981,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_981,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14310,c_14225])).

tff(c_14424,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13041,c_14421])).

tff(c_14431,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13506,c_14424])).

tff(c_13299,plain,(
    ! [A_854] :
      ( k2_relat_1(k2_funct_1(A_854)) = k1_relat_1(A_854)
      | ~ v2_funct_1(A_854)
      | ~ v1_funct_1(A_854)
      | ~ v1_relat_1(A_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13148,plain,(
    ! [B_826,A_827] :
      ( v5_relat_1(B_826,A_827)
      | ~ r1_tarski(k2_relat_1(B_826),A_827)
      | ~ v1_relat_1(B_826) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13157,plain,(
    ! [B_826] :
      ( v5_relat_1(B_826,k2_relat_1(B_826))
      | ~ v1_relat_1(B_826) ) ),
    inference(resolution,[status(thm)],[c_6,c_13148])).

tff(c_16092,plain,(
    ! [A_1064] :
      ( v5_relat_1(k2_funct_1(A_1064),k1_relat_1(A_1064))
      | ~ v1_relat_1(k2_funct_1(A_1064))
      | ~ v2_funct_1(A_1064)
      | ~ v1_funct_1(A_1064)
      | ~ v1_relat_1(A_1064) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13299,c_13157])).

tff(c_16095,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14431,c_16092])).

tff(c_16100,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_16095])).

tff(c_16101,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16100])).

tff(c_16104,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_16101])).

tff(c_16108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_16104])).

tff(c_16110,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16100])).

tff(c_16109,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_16100])).

tff(c_16449,plain,(
    ! [A_1092,A_1093] :
      ( r1_tarski(k1_relat_1(A_1092),A_1093)
      | ~ v5_relat_1(k2_funct_1(A_1092),A_1093)
      | ~ v1_relat_1(k2_funct_1(A_1092))
      | ~ v2_funct_1(A_1092)
      | ~ v1_funct_1(A_1092)
      | ~ v1_relat_1(A_1092) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13299,c_20])).

tff(c_17180,plain,(
    ! [A_1112] :
      ( r1_tarski(k1_relat_1(A_1112),k2_relat_1(k2_funct_1(A_1112)))
      | ~ v2_funct_1(A_1112)
      | ~ v1_funct_1(A_1112)
      | ~ v1_relat_1(A_1112)
      | ~ v1_relat_1(k2_funct_1(A_1112)) ) ),
    inference(resolution,[status(thm)],[c_13157,c_16449])).

tff(c_17188,plain,
    ( r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14431,c_17180])).

tff(c_17198,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16110,c_179,c_68,c_62,c_17188])).

tff(c_13089,plain,(
    ! [B_814,A_815] :
      ( k2_relat_1(B_814) = A_815
      | ~ r1_tarski(A_815,k2_relat_1(B_814))
      | ~ v5_relat_1(B_814,A_815)
      | ~ v1_relat_1(B_814) ) ),
    inference(resolution,[status(thm)],[c_13073,c_2])).

tff(c_17202,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17198,c_13089])).

tff(c_17210,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16110,c_16109,c_17202])).

tff(c_13899,plain,(
    ! [B_926,A_927] :
      ( m1_subset_1(B_926,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_926),A_927)))
      | ~ r1_tarski(k2_relat_1(B_926),A_927)
      | ~ v1_funct_1(B_926)
      | ~ v1_relat_1(B_926) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_17662,plain,(
    ! [A_1119,A_1120] :
      ( m1_subset_1(k2_funct_1(A_1119),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1119),A_1120)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1119)),A_1120)
      | ~ v1_funct_1(k2_funct_1(A_1119))
      | ~ v1_relat_1(k2_funct_1(A_1119))
      | ~ v2_funct_1(A_1119)
      | ~ v1_funct_1(A_1119)
      | ~ v1_relat_1(A_1119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_13899])).

tff(c_17692,plain,(
    ! [A_1120] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_1120)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1120)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_17662])).

tff(c_17712,plain,(
    ! [A_1121] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_1121)))
      | ~ r1_tarski('#skF_1',A_1121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_16110,c_149,c_17210,c_17692])).

tff(c_17736,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_17712,c_150])).

tff(c_17756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17736])).

tff(c_17758,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_13637])).

tff(c_13625,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_2',A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_20])).

tff(c_17781,plain,(
    ! [A_1124] :
      ( r1_tarski('#skF_2',A_1124)
      | ~ v5_relat_1('#skF_3',A_1124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_13625])).

tff(c_17804,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17758,c_17781])).

tff(c_18167,plain,(
    ! [B_1162,A_1163,C_1164] :
      ( k1_xboole_0 = B_1162
      | k1_relset_1(A_1163,B_1162,C_1164) = A_1163
      | ~ v1_funct_2(C_1164,A_1163,B_1162)
      | ~ m1_subset_1(C_1164,k1_zfmisc_1(k2_zfmisc_1(A_1163,B_1162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18173,plain,(
    ! [C_1164] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1164) = '#skF_1'
      | ~ v1_funct_2(C_1164,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1164,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_18167])).

tff(c_18201,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18173])).

tff(c_17819,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_17804,c_2])).

tff(c_17822,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_17819])).

tff(c_18218,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18201,c_17822])).

tff(c_18260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18218])).

tff(c_18353,plain,(
    ! [C_1179] :
      ( k1_relset_1('#skF_1','#skF_2',C_1179) = '#skF_1'
      | ~ v1_funct_2(C_1179,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1179,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_18173])).

tff(c_18356,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13041,c_18353])).

tff(c_18363,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13506,c_18356])).

tff(c_18372,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_3','#skF_1',A_26)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18363,c_54])).

tff(c_18384,plain,(
    ! [A_1180] :
      ( v1_funct_2('#skF_3','#skF_1',A_1180)
      | ~ r1_tarski('#skF_2',A_1180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_13596,c_18372])).

tff(c_18387,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18384,c_72])).

tff(c_18390,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17804,c_18387])).

tff(c_18391,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_13104,c_18390])).

tff(c_18392,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_18391])).

tff(c_18369,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_26)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18363,c_52])).

tff(c_18417,plain,(
    ! [A_1184] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_1184)))
      | ~ r1_tarski('#skF_2',A_1184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_13596,c_18369])).

tff(c_18448,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_18417])).

tff(c_18464,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17804,c_18448])).

tff(c_18466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18392,c_18464])).

tff(c_18467,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18391])).

tff(c_13273,plain,(
    ! [B_851,A_852,B_853] :
      ( v1_relat_1(k2_relat_1(B_851))
      | ~ v5_relat_1(B_851,k2_zfmisc_1(A_852,B_853))
      | ~ v1_relat_1(B_851) ) ),
    inference(resolution,[status(thm)],[c_13073,c_178])).

tff(c_13298,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_255,c_13273])).

tff(c_13610,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_13596,c_13298])).

tff(c_13635,plain,
    ( v1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_13610])).

tff(c_13647,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_13635])).

tff(c_18495,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18467,c_13647])).

tff(c_18468,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_18391])).

tff(c_18620,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18467,c_18468])).

tff(c_18623,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_18620,c_14])).

tff(c_18627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18495,c_18623])).

tff(c_18628,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17819])).

tff(c_18668,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18628,c_13104])).

tff(c_18707,plain,(
    ! [A_1198] : k2_zfmisc_1(A_1198,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18628,c_18628,c_10])).

tff(c_18741,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18707,c_13038])).

tff(c_18761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18668,c_18741])).

tff(c_18763,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_13635])).

tff(c_18837,plain,(
    ! [A_1205] :
      ( r1_tarski('#skF_2',A_1205)
      | ~ v5_relat_1('#skF_3',A_1205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_13625])).

tff(c_18849,plain,(
    ! [B_64] :
      ( r1_tarski('#skF_2',B_64)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_255,c_18837])).

tff(c_18861,plain,(
    ! [B_64] : r1_tarski('#skF_2',B_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18763,c_18849])).

tff(c_19580,plain,(
    ! [B_1227,A_1228,C_1229] :
      ( k1_xboole_0 = B_1227
      | k1_relset_1(A_1228,B_1227,C_1229) = A_1228
      | ~ v1_funct_2(C_1229,A_1228,B_1227)
      | ~ m1_subset_1(C_1229,k1_zfmisc_1(k2_zfmisc_1(A_1228,B_1227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_19586,plain,(
    ! [C_1229] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1229) = '#skF_1'
      | ~ v1_funct_2(C_1229,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1229,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13038,c_19580])).

tff(c_19628,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_19586])).

tff(c_18766,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18763,c_2])).

tff(c_18772,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_13104,c_18766])).

tff(c_19634,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19628,c_18772])).

tff(c_19660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18861,c_19634])).

tff(c_19757,plain,(
    ! [C_1237] :
      ( k1_relset_1('#skF_1','#skF_2',C_1237) = '#skF_1'
      | ~ v1_funct_2(C_1237,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1237,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_19586])).

tff(c_19760,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13041,c_19757])).

tff(c_19767,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_13506,c_19760])).

tff(c_19773,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_26)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19767,c_52])).

tff(c_19796,plain,(
    ! [A_1239] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_1239))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_18861,c_13596,c_19773])).

tff(c_19825,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_19796])).

tff(c_19776,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_3','#skF_1',A_26)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19767,c_54])).

tff(c_19785,plain,(
    ! [A_1238] : v1_funct_2('#skF_3','#skF_1',A_1238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_18861,c_13596,c_19776])).

tff(c_19788,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_19785,c_72])).

tff(c_19791,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_13104,c_19788])).

tff(c_19952,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19825,c_19791])).

tff(c_19977,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19952,c_13104])).

tff(c_19984,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19952,c_19952,c_12])).

tff(c_20118,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19984,c_13038])).

tff(c_20122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19977,c_20118])).

tff(c_20124,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_13049])).

tff(c_20142,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20124,c_20124,c_12])).

tff(c_20123,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13049])).

tff(c_20149,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20124,c_20124,c_20123])).

tff(c_20150,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20149])).

tff(c_20155,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20150,c_150])).

tff(c_20257,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20142,c_20155])).

tff(c_20143,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20124,c_20124,c_10])).

tff(c_21246,plain,(
    ! [B_1381,A_1382] :
      ( m1_subset_1(B_1381,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1381),A_1382)))
      | ~ r1_tarski(k2_relat_1(B_1381),A_1382)
      | ~ v1_funct_1(B_1381)
      | ~ v1_relat_1(B_1381) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_21490,plain,(
    ! [B_1410] :
      ( m1_subset_1(B_1410,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(B_1410),'#skF_3')
      | ~ v1_funct_1(B_1410)
      | ~ v1_relat_1(B_1410) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20143,c_21246])).

tff(c_21509,plain,(
    ! [B_1411] :
      ( m1_subset_1(B_1411,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1(B_1411)
      | ~ v5_relat_1(B_1411,'#skF_3')
      | ~ v1_relat_1(B_1411) ) ),
    inference(resolution,[status(thm)],[c_20,c_21490])).

tff(c_21524,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_21509,c_20257])).

tff(c_21541,plain,
    ( ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_21524])).

tff(c_21545,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21541])).

tff(c_21548,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_21545])).

tff(c_21552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_21548])).

tff(c_21554,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21541])).

tff(c_20652,plain,(
    ! [A_1330,B_1331,C_1332] :
      ( k2_relset_1(A_1330,B_1331,C_1332) = k2_relat_1(C_1332)
      | ~ m1_subset_1(C_1332,k1_zfmisc_1(k2_zfmisc_1(A_1330,B_1331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20833,plain,(
    ! [A_1361,C_1362] :
      ( k2_relset_1(A_1361,'#skF_3',C_1362) = k2_relat_1(C_1362)
      | ~ m1_subset_1(C_1362,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20143,c_20652])).

tff(c_20849,plain,(
    ! [A_1365] : k2_relset_1(A_1365,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_13041,c_20833])).

tff(c_20156,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20150,c_20150,c_60])).

tff(c_20856,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_20849,c_20156])).

tff(c_24914,plain,(
    ! [A_1527,A_1528] :
      ( m1_subset_1(k2_funct_1(A_1527),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1527),A_1528)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_1527)),A_1528)
      | ~ v1_funct_1(k2_funct_1(A_1527))
      | ~ v1_relat_1(k2_funct_1(A_1527))
      | ~ v2_funct_1(A_1527)
      | ~ v1_funct_1(A_1527)
      | ~ v1_relat_1(A_1527) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_21246])).

tff(c_24959,plain,(
    ! [A_1528] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_1528)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1528)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20856,c_24914])).

tff(c_24984,plain,(
    ! [A_1528] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1528) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_68,c_62,c_21554,c_149,c_20142,c_24959])).

tff(c_24986,plain,(
    ! [A_1529] : ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_1529) ),
    inference(negUnitSimplification,[status(thm)],[c_20257,c_24984])).

tff(c_25015,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_24986])).

tff(c_25016,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20149])).

tff(c_25026,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_179])).

tff(c_25032,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_68])).

tff(c_25031,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_62])).

tff(c_25028,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_149])).

tff(c_25057,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_25016,c_20143])).

tff(c_25977,plain,(
    ! [B_1652,A_1653] :
      ( m1_subset_1(B_1652,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1652),A_1653)))
      | ~ r1_tarski(k2_relat_1(B_1652),A_1653)
      | ~ v1_funct_1(B_1652)
      | ~ v1_relat_1(B_1652) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_27783,plain,(
    ! [B_1745] :
      ( m1_subset_1(B_1745,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(B_1745),'#skF_1')
      | ~ v1_funct_1(B_1745)
      | ~ v1_relat_1(B_1745) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25057,c_25977])).

tff(c_27905,plain,(
    ! [B_1751] :
      ( m1_subset_1(B_1751,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(B_1751)
      | ~ v5_relat_1(B_1751,'#skF_1')
      | ~ v1_relat_1(B_1751) ) ),
    inference(resolution,[status(thm)],[c_20,c_27783])).

tff(c_25027,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_150])).

tff(c_25147,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25057,c_25027])).

tff(c_27925,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v5_relat_1(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_27905,c_25147])).

tff(c_27939,plain,
    ( ~ v5_relat_1(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25028,c_27925])).

tff(c_27941,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_27939])).

tff(c_27944,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_27941])).

tff(c_27948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25026,c_25032,c_27944])).

tff(c_27950,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_27939])).

tff(c_25022,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_25016,c_13041])).

tff(c_25093,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_25016,c_20142])).

tff(c_25540,plain,(
    ! [A_1603,B_1604,C_1605] :
      ( k1_relset_1(A_1603,B_1604,C_1605) = k1_relat_1(C_1605)
      | ~ m1_subset_1(C_1605,k1_zfmisc_1(k2_zfmisc_1(A_1603,B_1604))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_25759,plain,(
    ! [B_1638,C_1639] :
      ( k1_relset_1('#skF_1',B_1638,C_1639) = k1_relat_1(C_1639)
      | ~ m1_subset_1(C_1639,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25093,c_25540])).

tff(c_25767,plain,(
    ! [B_1640] : k1_relset_1('#skF_1',B_1640,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_25022,c_25759])).

tff(c_25030,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_66])).

tff(c_25018,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25016,c_20124])).

tff(c_48,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_69,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_25646,plain,(
    ! [B_1617,C_1618] :
      ( k1_relset_1('#skF_1',B_1617,C_1618) = '#skF_1'
      | ~ v1_funct_2(C_1618,'#skF_1',B_1617)
      | ~ m1_subset_1(C_1618,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25018,c_25018,c_25018,c_25018,c_69])).

tff(c_25651,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_25030,c_25646])).

tff(c_25658,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25022,c_25651])).

tff(c_25774,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_25767,c_25658])).

tff(c_25252,plain,(
    ! [A_1560] :
      ( k2_relat_1(k2_funct_1(A_1560)) = k1_relat_1(A_1560)
      | ~ v2_funct_1(A_1560)
      | ~ v1_funct_1(A_1560)
      | ~ v1_relat_1(A_1560) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_25264,plain,(
    ! [A_1560,A_7] :
      ( v5_relat_1(k2_funct_1(A_1560),A_7)
      | ~ r1_tarski(k1_relat_1(A_1560),A_7)
      | ~ v1_relat_1(k2_funct_1(A_1560))
      | ~ v2_funct_1(A_1560)
      | ~ v1_funct_1(A_1560)
      | ~ v1_relat_1(A_1560) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25252,c_18])).

tff(c_27949,plain,(
    ~ v5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_27939])).

tff(c_27953,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_25264,c_27949])).

tff(c_27960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25026,c_25032,c_25031,c_27950,c_6,c_25774,c_27953])).

tff(c_27961,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_28376,plain,(
    ! [A_1824,B_1825,C_1826] :
      ( k2_relset_1(A_1824,B_1825,C_1826) = k2_relat_1(C_1826)
      | ~ m1_subset_1(C_1826,k1_zfmisc_1(k2_zfmisc_1(A_1824,B_1825))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28386,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_28376])).

tff(c_28396,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28386])).

tff(c_27962,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_28323,plain,(
    ! [A_1816,B_1817,C_1818] :
      ( k1_relset_1(A_1816,B_1817,C_1818) = k1_relat_1(C_1818)
      | ~ m1_subset_1(C_1818,k1_zfmisc_1(k2_zfmisc_1(A_1816,B_1817))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28340,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_27962,c_28323])).

tff(c_28782,plain,(
    ! [B_1870,C_1871,A_1872] :
      ( k1_xboole_0 = B_1870
      | v1_funct_2(C_1871,A_1872,B_1870)
      | k1_relset_1(A_1872,B_1870,C_1871) != A_1872
      | ~ m1_subset_1(C_1871,k1_zfmisc_1(k2_zfmisc_1(A_1872,B_1870))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28788,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_27962,c_28782])).

tff(c_28804,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28340,c_28788])).

tff(c_28805,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_28804])).

tff(c_28810,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28805])).

tff(c_28813,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_28810])).

tff(c_28816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_28396,c_28813])).

tff(c_28817,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_28805])).

tff(c_28080,plain,(
    ! [C_1773,B_1774,A_1775] :
      ( v5_relat_1(C_1773,B_1774)
      | ~ m1_subset_1(C_1773,k1_zfmisc_1(k2_zfmisc_1(A_1775,B_1774))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28115,plain,(
    ! [C_1780,B_1781] :
      ( v5_relat_1(C_1780,B_1781)
      | ~ m1_subset_1(C_1780,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_28080])).

tff(c_28119,plain,(
    ! [A_5,B_1781] :
      ( v5_relat_1(A_5,B_1781)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_28115])).

tff(c_28120,plain,(
    ! [B_1782,A_1783] :
      ( r1_tarski(k2_relat_1(B_1782),A_1783)
      | ~ v5_relat_1(B_1782,A_1783)
      | ~ v1_relat_1(B_1782) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27994,plain,(
    ! [A_5,A_1757,B_1758] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_1757,B_1758)) ) ),
    inference(resolution,[status(thm)],[c_16,c_27978])).

tff(c_28275,plain,(
    ! [B_1808,A_1809,B_1810] :
      ( v1_relat_1(k2_relat_1(B_1808))
      | ~ v5_relat_1(B_1808,k2_zfmisc_1(A_1809,B_1810))
      | ~ v1_relat_1(B_1808) ) ),
    inference(resolution,[status(thm)],[c_28120,c_27994])).

tff(c_28298,plain,(
    ! [A_5] :
      ( v1_relat_1(k2_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28119,c_28275])).

tff(c_28400,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28396,c_28298])).

tff(c_28416,plain,
    ( v1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_28400])).

tff(c_28426,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_28416])).

tff(c_28839,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28817,c_28426])).

tff(c_28858,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28817,c_28817,c_12])).

tff(c_27965,plain,(
    ! [A_1754,B_1755] :
      ( r1_tarski(A_1754,B_1755)
      | ~ m1_subset_1(A_1754,k1_zfmisc_1(B_1755)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27973,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_27965])).

tff(c_29025,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28858,c_27973])).

tff(c_29028,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28839,c_29025])).

tff(c_29030,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_28416])).

tff(c_28412,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_2',A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28396,c_20])).

tff(c_29063,plain,(
    ! [A_1882] :
      ( r1_tarski('#skF_2',A_1882)
      | ~ v5_relat_1('#skF_3',A_1882) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_28412])).

tff(c_29074,plain,(
    ! [B_1781] :
      ( r1_tarski('#skF_2',B_1781)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28119,c_29063])).

tff(c_29084,plain,(
    ! [B_1781] : r1_tarski('#skF_2',B_1781) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29030,c_29074])).

tff(c_28342,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_28323])).

tff(c_29971,plain,(
    ! [B_1951,A_1952,C_1953] :
      ( k1_xboole_0 = B_1951
      | k1_relset_1(A_1952,B_1951,C_1953) = A_1952
      | ~ v1_funct_2(C_1953,A_1952,B_1951)
      | ~ m1_subset_1(C_1953,k1_zfmisc_1(k2_zfmisc_1(A_1952,B_1951))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_29984,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_29971])).

tff(c_29997,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28342,c_29984])).

tff(c_29999,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_29997])).

tff(c_27993,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_27962,c_27978])).

tff(c_30128,plain,(
    ! [B_1959,C_1960,A_1961] :
      ( k1_xboole_0 = B_1959
      | v1_funct_2(C_1960,A_1961,B_1959)
      | k1_relset_1(A_1961,B_1959,C_1960) != A_1961
      | ~ m1_subset_1(C_1960,k1_zfmisc_1(k2_zfmisc_1(A_1961,B_1959))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30137,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_27962,c_30128])).

tff(c_30152,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28340,c_30137])).

tff(c_30153,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_30152])).

tff(c_30222,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30153])).

tff(c_30225,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_30222])).

tff(c_30228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_28396,c_30225])).

tff(c_30229,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30153])).

tff(c_30274,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30229,c_30229,c_10])).

tff(c_30457,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30274,c_27962])).

tff(c_28093,plain,(
    ! [C_1773,B_4] :
      ( v5_relat_1(C_1773,B_4)
      | ~ m1_subset_1(C_1773,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_28080])).

tff(c_30724,plain,(
    ! [C_1985,B_1986] :
      ( v5_relat_1(C_1985,B_1986)
      | ~ m1_subset_1(C_1985,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30229,c_28093])).

tff(c_30741,plain,(
    ! [B_1987] : v5_relat_1(k2_funct_1('#skF_3'),B_1987) ),
    inference(resolution,[status(thm)],[c_30457,c_30724])).

tff(c_29090,plain,(
    ! [B_1883] : r1_tarski('#skF_2',B_1883) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29030,c_29074])).

tff(c_29138,plain,(
    ! [B_1887] :
      ( B_1887 = '#skF_2'
      | ~ r1_tarski(B_1887,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_29090,c_2])).

tff(c_29153,plain,(
    ! [B_8] :
      ( k2_relat_1(B_8) = '#skF_2'
      | ~ v5_relat_1(B_8,'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_29138])).

tff(c_30748,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30741,c_29153])).

tff(c_30758,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27993,c_30748])).

tff(c_30773,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30758,c_26])).

tff(c_30789,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_29999,c_30773])).

tff(c_30823,plain,(
    ! [B_1781] : r1_tarski('#skF_1',B_1781) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30789,c_29084])).

tff(c_27977,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_27962,c_14])).

tff(c_28008,plain,(
    ! [B_1761,A_1762] :
      ( B_1761 = A_1762
      | ~ r1_tarski(B_1761,A_1762)
      | ~ r1_tarski(A_1762,B_1761) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28015,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_27977,c_28008])).

tff(c_28106,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28015])).

tff(c_30455,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30274,c_28106])).

tff(c_30875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30823,c_30455])).

tff(c_30876,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_29997])).

tff(c_29043,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_29030,c_2])).

tff(c_29047,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_29043])).

tff(c_30899,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30876,c_29047])).

tff(c_30926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29084,c_30899])).

tff(c_30927,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_29043])).

tff(c_46,plain,(
    ! [B_24,C_25,A_23] :
      ( k1_xboole_0 = B_24
      | v1_funct_2(C_25,A_23,B_24)
      | k1_relset_1(A_23,B_24,C_25) != A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_31935,plain,(
    ! [B_2057,C_2058,A_2059] :
      ( B_2057 = '#skF_3'
      | v1_funct_2(C_2058,A_2059,B_2057)
      | k1_relset_1(A_2059,B_2057,C_2058) != A_2059
      | ~ m1_subset_1(C_2058,k1_zfmisc_1(k2_zfmisc_1(A_2059,B_2057))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30927,c_46])).

tff(c_31947,plain,
    ( '#skF_3' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_27962,c_31935])).

tff(c_31958,plain,
    ( '#skF_3' = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28340,c_31947])).

tff(c_31959,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_31958])).

tff(c_31963,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_31959])).

tff(c_31966,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_31963])).

tff(c_31969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_28396,c_31966])).

tff(c_31970,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31959])).

tff(c_30948,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30927,c_30927,c_12])).

tff(c_31996,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31970,c_31970,c_30948])).

tff(c_28016,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_27973,c_28008])).

tff(c_28048,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28016])).

tff(c_32006,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31970,c_28048])).

tff(c_32286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_31996,c_32006])).

tff(c_32287,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_28015])).

tff(c_32290,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32287,c_27962])).

tff(c_32794,plain,(
    ! [A_2141,B_2142,C_2143] :
      ( k1_relset_1(A_2141,B_2142,C_2143) = k1_relat_1(C_2143)
      | ~ m1_subset_1(C_2143,k1_zfmisc_1(k2_zfmisc_1(A_2141,B_2142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36333,plain,(
    ! [C_2367] :
      ( k1_relset_1('#skF_2','#skF_1',C_2367) = k1_relat_1(C_2367)
      | ~ m1_subset_1(C_2367,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32287,c_32794])).

tff(c_36341,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32290,c_36333])).

tff(c_34596,plain,(
    ! [B_2282,C_2283,A_2284] :
      ( k1_xboole_0 = B_2282
      | v1_funct_2(C_2283,A_2284,B_2282)
      | k1_relset_1(A_2284,B_2282,C_2283) != A_2284
      | ~ m1_subset_1(C_2283,k1_zfmisc_1(k2_zfmisc_1(A_2284,B_2282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34602,plain,(
    ! [C_2283] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_2283,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2283) != '#skF_2'
      | ~ m1_subset_1(C_2283,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32287,c_34596])).

tff(c_34658,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_34602])).

tff(c_32301,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32287,c_8])).

tff(c_32356,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32301])).

tff(c_34694,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34658,c_32356])).

tff(c_34704,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34658,c_34658,c_10])).

tff(c_34798,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34704,c_32287])).

tff(c_34800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34694,c_34798])).

tff(c_34802,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34602])).

tff(c_33087,plain,(
    ! [C_2159] :
      ( k1_relset_1('#skF_2','#skF_1',C_2159) = k1_relat_1(C_2159)
      | ~ m1_subset_1(C_2159,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32287,c_32794])).

tff(c_33095,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32290,c_33087])).

tff(c_33395,plain,(
    ! [B_2183,C_2184,A_2185] :
      ( k1_xboole_0 = B_2183
      | v1_funct_2(C_2184,A_2185,B_2183)
      | k1_relset_1(A_2185,B_2183,C_2184) != A_2185
      | ~ m1_subset_1(C_2184,k1_zfmisc_1(k2_zfmisc_1(A_2185,B_2183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_33401,plain,(
    ! [C_2184] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_2184,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2184) != '#skF_2'
      | ~ m1_subset_1(C_2184,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32287,c_33395])).

tff(c_33445,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_33401])).

tff(c_32339,plain,(
    ! [C_2082,B_2083] :
      ( v5_relat_1(C_2082,B_2083)
      | ~ m1_subset_1(C_2082,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_28080])).

tff(c_32343,plain,(
    ! [A_5,B_2083] :
      ( v5_relat_1(A_5,B_2083)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_32339])).

tff(c_32388,plain,(
    ! [B_2092,A_2093] :
      ( r1_tarski(k2_relat_1(B_2092),A_2093)
      | ~ v5_relat_1(B_2092,A_2093)
      | ~ v1_relat_1(B_2092) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_27996,plain,(
    ! [C_1759] :
      ( v1_relat_1(C_1759)
      | ~ m1_subset_1(C_1759,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_27978])).

tff(c_28001,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_27996])).

tff(c_32415,plain,(
    ! [B_2092] :
      ( v1_relat_1(k2_relat_1(B_2092))
      | ~ v5_relat_1(B_2092,k1_xboole_0)
      | ~ v1_relat_1(B_2092) ) ),
    inference(resolution,[status(thm)],[c_32388,c_28001])).

tff(c_32893,plain,
    ( v1_relat_1('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32877,c_32415])).

tff(c_32914,plain,
    ( v1_relat_1('#skF_2')
    | ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_32893])).

tff(c_32922,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_32914])).

tff(c_32926,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32343,c_32922])).

tff(c_33468,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33445,c_32926])).

tff(c_33496,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33445,c_33445,c_12])).

tff(c_33588,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33496,c_27973])).

tff(c_33591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33468,c_33588])).

tff(c_34125,plain,(
    ! [C_2253] :
      ( v1_funct_2(C_2253,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2253) != '#skF_2'
      | ~ m1_subset_1(C_2253,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_33401])).

tff(c_34128,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_32290,c_34125])).

tff(c_34134,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33095,c_34128])).

tff(c_34135,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_34134])).

tff(c_34139,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_34135])).

tff(c_34142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_32877,c_34139])).

tff(c_34144,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_32914])).

tff(c_32896,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_2',A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32877,c_20])).

tff(c_34146,plain,(
    ! [A_2254] :
      ( r1_tarski('#skF_2',A_2254)
      | ~ v5_relat_1('#skF_3',A_2254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_32896])).

tff(c_34161,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34144,c_34146])).

tff(c_32812,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_32794])).

tff(c_34853,plain,(
    ! [B_2297,A_2298,C_2299] :
      ( k1_xboole_0 = B_2297
      | k1_relset_1(A_2298,B_2297,C_2299) = A_2298
      | ~ v1_funct_2(C_2299,A_2298,B_2297)
      | ~ m1_subset_1(C_2299,k1_zfmisc_1(k2_zfmisc_1(A_2298,B_2297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34866,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_34853])).

tff(c_34878,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32812,c_34866])).

tff(c_34880,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_34878])).

tff(c_34888,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_3','#skF_1',A_26)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34880,c_54])).

tff(c_34900,plain,(
    ! [A_2300] :
      ( v1_funct_2('#skF_3','#skF_1',A_2300)
      | ~ r1_tarski('#skF_2',A_2300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_32877,c_34888])).

tff(c_34903,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34900,c_72])).

tff(c_34906,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34161,c_34903])).

tff(c_34907,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_34802,c_34906])).

tff(c_34909,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_34907])).

tff(c_34885,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_26)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34880,c_52])).

tff(c_34967,plain,(
    ! [A_2306] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_2306)))
      | ~ r1_tarski('#skF_2',A_2306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_32877,c_34885])).

tff(c_34995,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_34967])).

tff(c_35009,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34161,c_34995])).

tff(c_35011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34909,c_35009])).

tff(c_35012,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34907])).

tff(c_34162,plain,(
    ! [B_2083] :
      ( r1_tarski('#skF_2',B_2083)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32343,c_34146])).

tff(c_34224,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_34162])).

tff(c_35030,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35012,c_34224])).

tff(c_35072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_35030])).

tff(c_35073,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34878])).

tff(c_34181,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_34161,c_2])).

tff(c_34184,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34181])).

tff(c_35092,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35073,c_34184])).

tff(c_35125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_35092])).

tff(c_35126,plain,(
    ! [B_2083] : r1_tarski('#skF_2',B_2083) ),
    inference(splitRight,[status(thm)],[c_34162])).

tff(c_35521,plain,(
    ! [B_2330,A_2331,C_2332] :
      ( k1_xboole_0 = B_2330
      | k1_relset_1(A_2331,B_2330,C_2332) = A_2331
      | ~ v1_funct_2(C_2332,A_2331,B_2330)
      | ~ m1_subset_1(C_2332,k1_zfmisc_1(k2_zfmisc_1(A_2331,B_2330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_35534,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_35521])).

tff(c_35545,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32812,c_35534])).

tff(c_35547,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_35545])).

tff(c_35552,plain,(
    ! [A_26] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_26)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35547,c_52])).

tff(c_35574,plain,(
    ! [A_2334] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_2334))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_35126,c_32877,c_35552])).

tff(c_35601,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_35574])).

tff(c_35555,plain,(
    ! [A_26] :
      ( v1_funct_2('#skF_3','#skF_1',A_26)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_26)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35547,c_54])).

tff(c_35564,plain,(
    ! [A_2333] : v1_funct_2('#skF_3','#skF_1',A_2333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_35126,c_32877,c_35555])).

tff(c_35568,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_35564,c_72])).

tff(c_35800,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35601,c_35568])).

tff(c_35801,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_35800])).

tff(c_35835,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35801,c_32356])).

tff(c_35845,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35801,c_35801,c_10])).

tff(c_35951,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35845,c_32287])).

tff(c_35953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35835,c_35951])).

tff(c_35954,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_35800])).

tff(c_35127,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_34162])).

tff(c_35179,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_35127,c_2])).

tff(c_35337,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_35179])).

tff(c_35978,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35954,c_35337])).

tff(c_36019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_35978])).

tff(c_36020,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_35545])).

tff(c_36027,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36020,c_35337])).

tff(c_36064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35126,c_36027])).

tff(c_36065,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_35179])).

tff(c_36306,plain,(
    ! [B_2363,C_2364,A_2365] :
      ( B_2363 = '#skF_3'
      | v1_funct_2(C_2364,A_2365,B_2363)
      | k1_relset_1(A_2365,B_2363,C_2364) != A_2365
      | ~ m1_subset_1(C_2364,k1_zfmisc_1(k2_zfmisc_1(A_2365,B_2363))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36065,c_46])).

tff(c_36318,plain,(
    ! [C_2364] :
      ( '#skF_3' = '#skF_1'
      | v1_funct_2(C_2364,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2364) != '#skF_2'
      | ~ m1_subset_1(C_2364,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32287,c_36306])).

tff(c_36713,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_36318])).

tff(c_36097,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36065,c_36065,c_12])).

tff(c_36742,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36713,c_36713,c_36097])).

tff(c_36765,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36713,c_28048])).

tff(c_37025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36742,c_36765])).

tff(c_38331,plain,(
    ! [C_2502] :
      ( v1_funct_2(C_2502,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_2502) != '#skF_2'
      | ~ m1_subset_1(C_2502,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_36318])).

tff(c_38334,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_32290,c_38331])).

tff(c_38340,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36341,c_38334])).

tff(c_38341,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_38340])).

tff(c_38345,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_38341])).

tff(c_38348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_32877,c_38345])).

tff(c_38349,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34181])).

tff(c_38370,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38349,c_32356])).

tff(c_38379,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38349,c_38349,c_12])).

tff(c_38478,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38379,c_32287])).

tff(c_38480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38370,c_38478])).

tff(c_38481,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32301])).

tff(c_38546,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_38481])).

tff(c_40,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_71,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_38567,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_1',A_23,'#skF_1')
      | A_23 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38546,c_38546,c_38546,c_38546,c_71])).

tff(c_38568,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_38567])).

tff(c_38688,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_38568])).

tff(c_38692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_38688])).

tff(c_38694,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_38567])).

tff(c_44,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_70,plain,(
    ! [C_25,B_24] :
      ( v1_funct_2(C_25,k1_xboole_0,B_24)
      | k1_relset_1(k1_xboole_0,B_24,C_25) != k1_xboole_0
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_39184,plain,(
    ! [C_2558,B_2559] :
      ( v1_funct_2(C_2558,'#skF_1',B_2559)
      | k1_relset_1('#skF_1',B_2559,C_2558) != '#skF_1'
      | ~ m1_subset_1(C_2558,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38546,c_38546,c_38546,c_70])).

tff(c_39266,plain,(
    ! [B_2570] :
      ( v1_funct_2('#skF_1','#skF_1',B_2570)
      | k1_relset_1('#skF_1',B_2570,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_38694,c_39184])).

tff(c_38920,plain,(
    ! [A_2528] :
      ( v1_funct_2('#skF_1',A_2528,'#skF_1')
      | A_2528 = '#skF_1' ) ),
    inference(splitRight,[status(thm)],[c_38567])).

tff(c_38482,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32301])).

tff(c_38490,plain,(
    ~ v1_funct_2(k1_xboole_0,'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38482,c_27961])).

tff(c_38550,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38490])).

tff(c_38930,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_38920,c_38550])).

tff(c_38931,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38930,c_38550])).

tff(c_39278,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_39266,c_38931])).

tff(c_38561,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38546,c_12])).

tff(c_38718,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38561,c_64])).

tff(c_39002,plain,(
    ! [C_2538,B_2539] :
      ( v5_relat_1(C_2538,B_2539)
      | ~ m1_subset_1(C_2538,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_28093])).

tff(c_39010,plain,(
    ! [B_2539] : v5_relat_1('#skF_3',B_2539) ),
    inference(resolution,[status(thm)],[c_38718,c_39002])).

tff(c_38552,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38482])).

tff(c_38742,plain,(
    ! [A_2520] :
      ( k1_relat_1(k2_funct_1(A_2520)) = k2_relat_1(A_2520)
      | ~ v2_funct_1(A_2520)
      | ~ v1_funct_1(A_2520)
      | ~ v1_relat_1(A_2520) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38751,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38552,c_38742])).

tff(c_38755,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_38751])).

tff(c_38812,plain,(
    ! [A_7] :
      ( r1_tarski(k1_relat_1('#skF_1'),A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38755,c_20])).

tff(c_38822,plain,(
    ! [A_7] :
      ( r1_tarski(k1_relat_1('#skF_1'),A_7)
      | ~ v5_relat_1('#skF_3',A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_38812])).

tff(c_39045,plain,(
    ! [A_7] : r1_tarski(k1_relat_1('#skF_1'),A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39010,c_38822])).

tff(c_28002,plain,(
    ! [A_1760] :
      ( v1_relat_1(A_1760)
      | ~ r1_tarski(A_1760,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_27996])).

tff(c_28007,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_28002])).

tff(c_38558,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_28007])).

tff(c_38485,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38482,c_38482,c_32290])).

tff(c_38536,plain,(
    ! [B_4] : v5_relat_1(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_38485,c_28093])).

tff(c_38548,plain,(
    ! [B_4] : v5_relat_1('#skF_1',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38536])).

tff(c_38845,plain,(
    ! [A_2523] :
      ( k2_relat_1(k2_funct_1(A_2523)) = k1_relat_1(A_2523)
      | ~ v2_funct_1(A_2523)
      | ~ v1_funct_1(A_2523)
      | ~ v1_relat_1(A_2523) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38863,plain,
    ( k2_relat_1('#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38552,c_38845])).

tff(c_38867,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_38863])).

tff(c_38871,plain,(
    ! [A_7] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_7)
      | ~ v5_relat_1('#skF_1',A_7)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38867,c_20])).

tff(c_38887,plain,(
    ! [A_2524] : r1_tarski(k1_relat_1('#skF_3'),A_2524) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38558,c_38548,c_38871])).

tff(c_39081,plain,(
    ! [A_2550] :
      ( k1_relat_1('#skF_3') = A_2550
      | ~ r1_tarski(A_2550,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38887,c_2])).

tff(c_39098,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_39045,c_39081])).

tff(c_39283,plain,(
    ! [B_2571,A_2572] :
      ( v1_funct_2(B_2571,k1_relat_1(B_2571),A_2572)
      | ~ r1_tarski(k2_relat_1(B_2571),A_2572)
      | ~ v1_funct_1(B_2571)
      | ~ v1_relat_1(B_2571) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_39289,plain,(
    ! [A_2572] :
      ( v1_funct_2('#skF_3',k1_relat_1('#skF_1'),A_2572)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_2572)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39098,c_39283])).

tff(c_39296,plain,(
    ! [A_2573] : v1_funct_2('#skF_3',k1_relat_1('#skF_1'),A_2573) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_39045,c_38755,c_39289])).

tff(c_38918,plain,(
    ! [C_25,A_23] :
      ( C_25 = '#skF_1'
      | ~ v1_funct_2(C_25,A_23,'#skF_1')
      | A_23 = '#skF_1'
      | ~ m1_subset_1(C_25,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38546,c_38546,c_38546,c_72])).

tff(c_39299,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_39296,c_38918])).

tff(c_39302,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38718,c_39299])).

tff(c_39303,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_39302])).

tff(c_39311,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39303,c_39045])).

tff(c_38716,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38561,c_28048])).

tff(c_39375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39311,c_38716])).

tff(c_39376,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_39302])).

tff(c_38934,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38930,c_66])).

tff(c_39064,plain,(
    ! [B_2548,C_2549] :
      ( k1_relset_1('#skF_1',B_2548,C_2549) = '#skF_1'
      | ~ v1_funct_2(C_2549,'#skF_1',B_2548)
      | ~ m1_subset_1(C_2549,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38546,c_38546,c_38546,c_38546,c_69])).

tff(c_39066,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38934,c_39064])).

tff(c_39072,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38718,c_39066])).

tff(c_39381,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39376,c_39072])).

tff(c_39395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39278,c_39381])).

tff(c_39396,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38481])).

tff(c_39397,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38481])).

tff(c_39418,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39396,c_39397])).

tff(c_39413,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39396,c_39396,c_10])).

tff(c_39483,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39413,c_64])).

tff(c_39629,plain,(
    ! [C_2584,A_2585] :
      ( C_2584 = '#skF_2'
      | ~ v1_funct_2(C_2584,A_2585,'#skF_2')
      | A_2585 = '#skF_2'
      | ~ m1_subset_1(C_2584,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39396,c_39396,c_39396,c_39396,c_72])).

tff(c_39631,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_39629])).

tff(c_39634,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39483,c_39631])).

tff(c_39635,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_39418,c_39634])).

tff(c_39481,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39413,c_28048])).

tff(c_39643,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39635,c_39481])).

tff(c_39660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_39643])).

tff(c_39661,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28016])).

tff(c_39664,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39661,c_64])).

tff(c_40072,plain,(
    ! [A_2647,B_2648,C_2649] :
      ( k2_relset_1(A_2647,B_2648,C_2649) = k2_relat_1(C_2649)
      | ~ m1_subset_1(C_2649,k1_zfmisc_1(k2_zfmisc_1(A_2647,B_2648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40198,plain,(
    ! [C_2661] :
      ( k2_relset_1('#skF_1','#skF_2',C_2661) = k2_relat_1(C_2661)
      | ~ m1_subset_1(C_2661,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39661,c_40072])).

tff(c_40201,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_39664,c_40198])).

tff(c_40207,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_40201])).

tff(c_40171,plain,(
    ! [A_2657,B_2658,C_2659] :
      ( k1_relset_1(A_2657,B_2658,C_2659) = k1_relat_1(C_2659)
      | ~ m1_subset_1(C_2659,k1_zfmisc_1(k2_zfmisc_1(A_2657,B_2658))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40188,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_27962,c_40171])).

tff(c_40876,plain,(
    ! [B_2729,C_2730,A_2731] :
      ( k1_xboole_0 = B_2729
      | v1_funct_2(C_2730,A_2731,B_2729)
      | k1_relset_1(A_2731,B_2729,C_2730) != A_2731
      | ~ m1_subset_1(C_2730,k1_zfmisc_1(k2_zfmisc_1(A_2731,B_2729))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40885,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_27962,c_40876])).

tff(c_40898,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40188,c_40885])).

tff(c_40899,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_40898])).

tff(c_40902,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40899])).

tff(c_40905,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_40902])).

tff(c_40908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_40207,c_40905])).

tff(c_40909,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40899])).

tff(c_39701,plain,(
    ! [B_2588,A_2589] :
      ( k1_xboole_0 = B_2588
      | k1_xboole_0 = A_2589
      | k2_zfmisc_1(A_2589,B_2588) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39704,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_39661,c_39701])).

tff(c_39715,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_39704])).

tff(c_40960,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40909,c_39715])).

tff(c_40965,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40909,c_40909,c_12])).

tff(c_41045,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40965,c_39661])).

tff(c_41047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40960,c_41045])).

tff(c_41049,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_39704])).

tff(c_41054,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41049,c_41049,c_12])).

tff(c_41186,plain,(
    ! [C_2750,B_2751,A_2752] :
      ( v5_relat_1(C_2750,B_2751)
      | ~ m1_subset_1(C_2750,k1_zfmisc_1(k2_zfmisc_1(A_2752,B_2751))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41241,plain,(
    ! [C_2763,B_2764] :
      ( v5_relat_1(C_2763,B_2764)
      | ~ m1_subset_1(C_2763,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41054,c_41186])).

tff(c_41250,plain,(
    ! [B_2764] : v5_relat_1('#skF_3',B_2764) ),
    inference(resolution,[status(thm)],[c_39664,c_41241])).

tff(c_41055,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41049,c_41049,c_10])).

tff(c_41438,plain,(
    ! [A_2793,B_2794,C_2795] :
      ( k2_relset_1(A_2793,B_2794,C_2795) = k2_relat_1(C_2795)
      | ~ m1_subset_1(C_2795,k1_zfmisc_1(k2_zfmisc_1(A_2793,B_2794))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_41549,plain,(
    ! [A_2819,C_2820] :
      ( k2_relset_1(A_2819,'#skF_3',C_2820) = k2_relat_1(C_2820)
      | ~ m1_subset_1(C_2820,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41055,c_41438])).

tff(c_41560,plain,(
    ! [A_2821] : k2_relset_1(A_2821,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_39664,c_41549])).

tff(c_41048,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_39704])).

tff(c_41075,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41049,c_41049,c_41048])).

tff(c_41076,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_41075])).

tff(c_41081,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41076,c_41076,c_60])).

tff(c_41567,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_41560,c_41081])).

tff(c_41606,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_3',A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41567,c_20])).

tff(c_41622,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_41250,c_41606])).

tff(c_41160,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41054,c_41076,c_41054,c_41076,c_28015])).

tff(c_41161,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_41160])).

tff(c_41627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41622,c_41161])).

tff(c_41628,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_41160])).

tff(c_41078,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41076,c_27977])).

tff(c_41128,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41054,c_41078])).

tff(c_41136,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_41128,c_2])).

tff(c_41159,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_41136])).

tff(c_41668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_41628,c_41159])).

tff(c_41669,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_41136])).

tff(c_41844,plain,(
    ! [A_2861] :
      ( k2_relat_1(k2_funct_1(A_2861)) = k1_relat_1(A_2861)
      | ~ v2_funct_1(A_2861)
      | ~ v1_funct_1(A_2861)
      | ~ v1_relat_1(A_2861) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_41865,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_41669,c_41844])).

tff(c_41869,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_62,c_41865])).

tff(c_42480,plain,(
    ! [A_2917,B_2918,C_2919] :
      ( k2_relset_1(A_2917,B_2918,C_2919) = k2_relat_1(C_2919)
      | ~ m1_subset_1(C_2919,k1_zfmisc_1(k2_zfmisc_1(A_2917,B_2918))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42598,plain,(
    ! [A_2927,C_2928] :
      ( k2_relset_1(A_2927,'#skF_3',C_2928) = k2_relat_1(C_2928)
      | ~ m1_subset_1(C_2928,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41055,c_42480])).

tff(c_42600,plain,(
    ! [A_2927] : k2_relset_1(A_2927,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_39664,c_42598])).

tff(c_42607,plain,(
    ! [A_2929] : k2_relset_1(A_2929,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41869,c_42600])).

tff(c_42614,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_42607,c_41081])).

tff(c_41768,plain,(
    ! [C_2843,B_2844,A_2845] :
      ( v5_relat_1(C_2843,B_2844)
      | ~ m1_subset_1(C_2843,k1_zfmisc_1(k2_zfmisc_1(A_2845,B_2844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41780,plain,(
    ! [C_2846,B_2847] :
      ( v5_relat_1(C_2846,B_2847)
      | ~ m1_subset_1(C_2846,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41054,c_41768])).

tff(c_41786,plain,(
    ! [B_2847] : v5_relat_1('#skF_3',B_2847) ),
    inference(resolution,[status(thm)],[c_39664,c_41780])).

tff(c_41883,plain,(
    ! [A_7] :
      ( r1_tarski(k1_relat_1('#skF_3'),A_7)
      | ~ v5_relat_1('#skF_3',A_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41869,c_20])).

tff(c_41893,plain,(
    ! [A_7] : r1_tarski(k1_relat_1('#skF_3'),A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_41786,c_41883])).

tff(c_42641,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42614,c_41893])).

tff(c_42643,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42614,c_41869])).

tff(c_42806,plain,(
    ! [B_2939,A_2940] :
      ( v1_funct_2(B_2939,k1_relat_1(B_2939),A_2940)
      | ~ r1_tarski(k2_relat_1(B_2939),A_2940)
      | ~ v1_funct_1(B_2939)
      | ~ v1_relat_1(B_2939) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42812,plain,(
    ! [A_2940] :
      ( v1_funct_2('#skF_3','#skF_3',A_2940)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_2940)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42614,c_42806])).

tff(c_42818,plain,(
    ! [A_2940] : v1_funct_2('#skF_3','#skF_3',A_2940) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27995,c_68,c_42641,c_42643,c_42812])).

tff(c_41080,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41076,c_27961])).

tff(c_41673,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41669,c_41080])).

tff(c_42821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42818,c_41673])).

tff(c_42822,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_41075])).

tff(c_42823,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_41075])).

tff(c_42843,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_42823])).

tff(c_42830,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_27995])).

tff(c_42838,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_68])).

tff(c_42837,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_62])).

tff(c_42829,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_27993])).

tff(c_42868,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_42822,c_41055])).

tff(c_42832,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_27962])).

tff(c_42945,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42868,c_42832])).

tff(c_42888,plain,(
    ! [B_2945] : k2_zfmisc_1('#skF_1',B_2945) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_42822,c_41054])).

tff(c_32,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42987,plain,(
    ! [C_2954,B_2955] :
      ( v5_relat_1(C_2954,B_2955)
      | ~ m1_subset_1(C_2954,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42888,c_32])).

tff(c_42995,plain,(
    ! [B_2955] : v5_relat_1(k2_funct_1('#skF_1'),B_2955) ),
    inference(resolution,[status(thm)],[c_42945,c_42987])).

tff(c_42827,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_42822,c_39664])).

tff(c_42996,plain,(
    ! [B_2955] : v5_relat_1('#skF_1',B_2955) ),
    inference(resolution,[status(thm)],[c_42827,c_42987])).

tff(c_42886,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_42822,c_41054])).

tff(c_43443,plain,(
    ! [A_3013,B_3014,C_3015] :
      ( k2_relset_1(A_3013,B_3014,C_3015) = k2_relat_1(C_3015)
      | ~ m1_subset_1(C_3015,k1_zfmisc_1(k2_zfmisc_1(A_3013,B_3014))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_43679,plain,(
    ! [B_3043,C_3044] :
      ( k2_relset_1('#skF_1',B_3043,C_3044) = k2_relat_1(C_3044)
      | ~ m1_subset_1(C_3044,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42886,c_43443])).

tff(c_43690,plain,(
    ! [B_3045] : k2_relset_1('#skF_1',B_3045,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42827,c_43679])).

tff(c_42835,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_60])).

tff(c_43697,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_43690,c_42835])).

tff(c_43745,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_2',A_7)
      | ~ v5_relat_1('#skF_1',A_7)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43697,c_20])).

tff(c_43808,plain,(
    ! [A_3049] : r1_tarski('#skF_2',A_3049) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42830,c_42996,c_43745])).

tff(c_43947,plain,(
    ! [A_3060] :
      ( A_3060 = '#skF_2'
      | ~ r1_tarski(A_3060,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_43808,c_2])).

tff(c_44038,plain,(
    ! [B_3068] :
      ( k2_relat_1(B_3068) = '#skF_2'
      | ~ v5_relat_1(B_3068,'#skF_2')
      | ~ v1_relat_1(B_3068) ) ),
    inference(resolution,[status(thm)],[c_20,c_43947])).

tff(c_44126,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42995,c_44038])).

tff(c_44190,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42829,c_44126])).

tff(c_44347,plain,
    ( k1_relat_1('#skF_1') = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44190,c_26])).

tff(c_44373,plain,(
    k1_relat_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42830,c_42838,c_42837,c_44347])).

tff(c_43346,plain,(
    ! [A_3003,B_3004,C_3005] :
      ( k1_relset_1(A_3003,B_3004,C_3005) = k1_relat_1(C_3005)
      | ~ m1_subset_1(C_3005,k1_zfmisc_1(k2_zfmisc_1(A_3003,B_3004))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44387,plain,(
    ! [A_3069,B_3070,A_3071] :
      ( k1_relset_1(A_3069,B_3070,A_3071) = k1_relat_1(A_3071)
      | ~ r1_tarski(A_3071,k2_zfmisc_1(A_3069,B_3070)) ) ),
    inference(resolution,[status(thm)],[c_16,c_43346])).

tff(c_44925,plain,(
    ! [B_3102,A_3103] :
      ( k1_relset_1('#skF_1',B_3102,A_3103) = k1_relat_1(A_3103)
      | ~ r1_tarski(A_3103,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42886,c_44387])).

tff(c_44936,plain,(
    ! [B_3102] : k1_relset_1('#skF_1',B_3102,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_44925])).

tff(c_44944,plain,(
    ! [B_3104] : k1_relset_1('#skF_1',B_3104,'#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44373,c_44936])).

tff(c_42836,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_66])).

tff(c_42824,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42822,c_41049])).

tff(c_43765,plain,(
    ! [B_3046,C_3047] :
      ( k1_relset_1('#skF_1',B_3046,C_3047) = '#skF_1'
      | ~ v1_funct_2(C_3047,'#skF_1',B_3046)
      | ~ m1_subset_1(C_3047,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42824,c_42824,c_42824,c_42824,c_69])).

tff(c_43774,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42836,c_43765])).

tff(c_43787,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42827,c_43774])).

tff(c_44948,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_44944,c_43787])).

tff(c_44955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42843,c_44948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.20/6.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.63/6.24  
% 14.63/6.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.63/6.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 14.63/6.24  
% 14.63/6.24  %Foreground sorts:
% 14.63/6.24  
% 14.63/6.24  
% 14.63/6.24  %Background operators:
% 14.63/6.24  
% 14.63/6.24  
% 14.63/6.24  %Foreground operators:
% 14.63/6.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.63/6.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.63/6.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.63/6.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.63/6.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.63/6.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.63/6.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.63/6.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.63/6.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.63/6.24  tff('#skF_2', type, '#skF_2': $i).
% 14.63/6.24  tff('#skF_3', type, '#skF_3': $i).
% 14.63/6.24  tff('#skF_1', type, '#skF_1': $i).
% 14.63/6.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.63/6.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 14.63/6.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.63/6.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.63/6.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.63/6.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.63/6.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.63/6.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.63/6.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.63/6.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.63/6.24  
% 14.95/6.31  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 14.95/6.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.95/6.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.95/6.31  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 14.95/6.31  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.95/6.31  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 14.95/6.31  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.95/6.31  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.95/6.31  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.95/6.31  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.95/6.31  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 14.95/6.31  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 14.95/6.31  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 14.95/6.31  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.95/6.31  tff(c_27978, plain, (![C_1756, A_1757, B_1758]: (v1_relat_1(C_1756) | ~m1_subset_1(C_1756, k1_zfmisc_1(k2_zfmisc_1(A_1757, B_1758))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.95/6.31  tff(c_27995, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_27978])).
% 14.95/6.31  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.95/6.31  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.95/6.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.95/6.31  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.95/6.31  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.95/6.31  tff(c_32858, plain, (![A_2147, B_2148, C_2149]: (k2_relset_1(A_2147, B_2148, C_2149)=k2_relat_1(C_2149) | ~m1_subset_1(C_2149, k1_zfmisc_1(k2_zfmisc_1(A_2147, B_2148))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_32868, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_32858])).
% 14.95/6.31  tff(c_32877, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32868])).
% 14.95/6.31  tff(c_28, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.95/6.31  tff(c_166, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.95/6.31  tff(c_179, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_166])).
% 14.95/6.31  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.95/6.31  tff(c_463, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_478, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_463])).
% 14.95/6.31  tff(c_912, plain, (![B_162, A_163, C_164]: (k1_xboole_0=B_162 | k1_relset_1(A_163, B_162, C_164)=A_163 | ~v1_funct_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_922, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_912])).
% 14.95/6.31  tff(c_933, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_478, c_922])).
% 14.95/6.31  tff(c_935, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_933])).
% 14.95/6.31  tff(c_26, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_24, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.95/6.31  tff(c_409, plain, (![A_94]: (k2_relat_1(k2_funct_1(A_94))=k1_relat_1(A_94) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_304, plain, (![B_76, A_77]: (v5_relat_1(B_76, A_77) | ~r1_tarski(k2_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_313, plain, (![B_76]: (v5_relat_1(B_76, k2_relat_1(B_76)) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_6, c_304])).
% 14.95/6.31  tff(c_3080, plain, (![A_293]: (v5_relat_1(k2_funct_1(A_293), k1_relat_1(A_293)) | ~v1_relat_1(k2_funct_1(A_293)) | ~v2_funct_1(A_293) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(superposition, [status(thm), theory('equality')], [c_409, c_313])).
% 14.95/6.31  tff(c_3083, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_935, c_3080])).
% 14.95/6.31  tff(c_3088, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_3083])).
% 14.95/6.31  tff(c_3089, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3088])).
% 14.95/6.31  tff(c_3092, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_3089])).
% 14.95/6.31  tff(c_3096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_3092])).
% 14.95/6.31  tff(c_3098, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3088])).
% 14.95/6.31  tff(c_103, plain, (![A_33]: (v1_funct_1(k2_funct_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.95/6.31  tff(c_58, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 14.95/6.31  tff(c_102, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 14.95/6.31  tff(c_106, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_102])).
% 14.95/6.31  tff(c_109, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_106])).
% 14.95/6.31  tff(c_131, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.95/6.31  tff(c_138, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_131])).
% 14.95/6.31  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_138])).
% 14.95/6.31  tff(c_149, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 14.95/6.31  tff(c_553, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_560, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_553])).
% 14.95/6.31  tff(c_569, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_560])).
% 14.95/6.31  tff(c_723, plain, (![B_138, A_139]: (m1_subset_1(B_138, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_138), A_139))) | ~r1_tarski(k2_relat_1(B_138), A_139) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_5261, plain, (![A_346, A_347]: (m1_subset_1(k2_funct_1(A_346), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_346), A_347))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_346)), A_347) | ~v1_funct_1(k2_funct_1(A_346)) | ~v1_relat_1(k2_funct_1(A_346)) | ~v2_funct_1(A_346) | ~v1_funct_1(A_346) | ~v1_relat_1(A_346))), inference(superposition, [status(thm), theory('equality')], [c_28, c_723])).
% 14.95/6.31  tff(c_5294, plain, (![A_347]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_347))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_347) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_5261])).
% 14.95/6.31  tff(c_5383, plain, (![A_350]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_350))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_350))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_3098, c_149, c_5294])).
% 14.95/6.31  tff(c_148, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 14.95/6.31  tff(c_150, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_148])).
% 14.95/6.31  tff(c_5423, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_5383, c_150])).
% 14.95/6.31  tff(c_5427, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_5423])).
% 14.95/6.31  tff(c_5433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_6, c_935, c_5427])).
% 14.95/6.31  tff(c_5434, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_933])).
% 14.95/6.31  tff(c_18, plain, (![B_8, A_7]: (v5_relat_1(B_8, A_7) | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_579, plain, (![A_7]: (v5_relat_1('#skF_3', A_7) | ~r1_tarski('#skF_2', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_18])).
% 14.95/6.31  tff(c_613, plain, (![A_122]: (v5_relat_1('#skF_3', A_122) | ~r1_tarski('#skF_2', A_122))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_579])).
% 14.95/6.31  tff(c_282, plain, (![B_72, A_73]: (r1_tarski(k2_relat_1(B_72), A_73) | ~v5_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.95/6.31  tff(c_180, plain, (![C_49]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 14.95/6.31  tff(c_185, plain, (![A_5]: (v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_180])).
% 14.95/6.31  tff(c_300, plain, (![B_72]: (v1_relat_1(k2_relat_1(B_72)) | ~v5_relat_1(B_72, k1_xboole_0) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_282, c_185])).
% 14.95/6.31  tff(c_582, plain, (v1_relat_1('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_569, c_300])).
% 14.95/6.31  tff(c_595, plain, (v1_relat_1('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_582])).
% 14.95/6.31  tff(c_600, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_595])).
% 14.95/6.31  tff(c_621, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_613, c_600])).
% 14.95/6.31  tff(c_5448, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5434, c_621])).
% 14.95/6.31  tff(c_5477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5448])).
% 14.95/6.31  tff(c_5479, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_595])).
% 14.95/6.31  tff(c_20, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_585, plain, (![A_7]: (r1_tarski('#skF_2', A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_20])).
% 14.95/6.31  tff(c_5496, plain, (![A_354]: (r1_tarski('#skF_2', A_354) | ~v5_relat_1('#skF_3', A_354))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_585])).
% 14.95/6.31  tff(c_5515, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_5479, c_5496])).
% 14.95/6.31  tff(c_5848, plain, (![B_397, A_398, C_399]: (k1_xboole_0=B_397 | k1_relset_1(A_398, B_397, C_399)=A_398 | ~v1_funct_2(C_399, A_398, B_397) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_398, B_397))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_5858, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_5848])).
% 14.95/6.31  tff(c_5869, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_478, c_5858])).
% 14.95/6.31  tff(c_5871, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5869])).
% 14.95/6.31  tff(c_54, plain, (![B_27, A_26]: (v1_funct_2(B_27, k1_relat_1(B_27), A_26) | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_5879, plain, (![A_26]: (v1_funct_2('#skF_3', '#skF_1', A_26) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5871, c_54])).
% 14.95/6.31  tff(c_5891, plain, (![A_400]: (v1_funct_2('#skF_3', '#skF_1', A_400) | ~r1_tarski('#skF_2', A_400))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_569, c_5879])).
% 14.95/6.31  tff(c_42, plain, (![C_25, A_23]: (k1_xboole_0=C_25 | ~v1_funct_2(C_25, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_72, plain, (![C_25, A_23]: (k1_xboole_0=C_25 | ~v1_funct_2(C_25, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 14.95/6.31  tff(c_5894, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_5891, c_72])).
% 14.95/6.31  tff(c_5897, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5515, c_5894])).
% 14.95/6.31  tff(c_5898, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_5897])).
% 14.95/6.31  tff(c_52, plain, (![B_27, A_26]: (m1_subset_1(B_27, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_27), A_26))) | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_5876, plain, (![A_26]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_26))) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5871, c_52])).
% 14.95/6.31  tff(c_5903, plain, (![A_401]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_401))) | ~r1_tarski('#skF_2', A_401))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_569, c_5876])).
% 14.95/6.31  tff(c_5928, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_5903])).
% 14.95/6.31  tff(c_5941, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_5515, c_5928])).
% 14.95/6.31  tff(c_5943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5898, c_5941])).
% 14.95/6.31  tff(c_5944, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5897])).
% 14.95/6.31  tff(c_5946, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5944])).
% 14.95/6.31  tff(c_235, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.95/6.31  tff(c_251, plain, (![C_63, B_64]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_235])).
% 14.95/6.31  tff(c_255, plain, (![A_5, B_64]: (v5_relat_1(A_5, B_64) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_251])).
% 14.95/6.31  tff(c_178, plain, (![A_5, A_47, B_48]: (v1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_47, B_48)))), inference(resolution, [status(thm)], [c_16, c_166])).
% 14.95/6.31  tff(c_439, plain, (![B_97, A_98, B_99]: (v1_relat_1(k2_relat_1(B_97)) | ~v5_relat_1(B_97, k2_zfmisc_1(A_98, B_99)) | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_282, c_178])).
% 14.95/6.31  tff(c_462, plain, (![A_5]: (v1_relat_1(k2_relat_1(A_5)) | ~v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_255, c_439])).
% 14.95/6.31  tff(c_573, plain, (v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_569, c_462])).
% 14.95/6.31  tff(c_589, plain, (v1_relat_1('#skF_2') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_573])).
% 14.95/6.31  tff(c_599, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_589])).
% 14.95/6.31  tff(c_5993, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5946, c_599])).
% 14.95/6.31  tff(c_6023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5993])).
% 14.95/6.31  tff(c_6024, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5944])).
% 14.95/6.31  tff(c_6049, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6024, c_599])).
% 14.95/6.31  tff(c_5945, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_5897])).
% 14.95/6.31  tff(c_6151, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6024, c_5945])).
% 14.95/6.31  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.95/6.31  tff(c_6154, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_6151, c_14])).
% 14.95/6.31  tff(c_6158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6049, c_6154])).
% 14.95/6.31  tff(c_6159, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5869])).
% 14.95/6.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.95/6.31  tff(c_5530, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_5515, c_2])).
% 14.95/6.31  tff(c_5533, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_5530])).
% 14.95/6.31  tff(c_6178, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6159, c_5533])).
% 14.95/6.31  tff(c_6209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6178])).
% 14.95/6.31  tff(c_6210, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5530])).
% 14.95/6.31  tff(c_6215, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6210, c_599])).
% 14.95/6.31  tff(c_6238, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6210, c_6210, c_10])).
% 14.95/6.31  tff(c_153, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.95/6.31  tff(c_161, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_153])).
% 14.95/6.31  tff(c_6271, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6238, c_161])).
% 14.95/6.31  tff(c_6274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6215, c_6271])).
% 14.95/6.31  tff(c_6276, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_589])).
% 14.95/6.31  tff(c_6306, plain, (![A_418]: (r1_tarski('#skF_2', A_418) | ~v5_relat_1('#skF_3', A_418))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_585])).
% 14.95/6.31  tff(c_6317, plain, (![B_64]: (r1_tarski('#skF_2', B_64) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_255, c_6306])).
% 14.95/6.31  tff(c_6327, plain, (![B_64]: (r1_tarski('#skF_2', B_64))), inference(demodulation, [status(thm), theory('equality')], [c_6276, c_6317])).
% 14.95/6.31  tff(c_7096, plain, (![B_480, A_481, C_482]: (k1_xboole_0=B_480 | k1_relset_1(A_481, B_480, C_482)=A_481 | ~v1_funct_2(C_482, A_481, B_480) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_481, B_480))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_7106, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_7096])).
% 14.95/6.31  tff(c_7117, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_478, c_7106])).
% 14.95/6.31  tff(c_7119, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_7117])).
% 14.95/6.31  tff(c_8548, plain, (![A_567, A_568]: (v5_relat_1(k2_funct_1(A_567), A_568) | ~r1_tarski(k1_relat_1(A_567), A_568) | ~v1_relat_1(k2_funct_1(A_567)) | ~v2_funct_1(A_567) | ~v1_funct_1(A_567) | ~v1_relat_1(A_567))), inference(superposition, [status(thm), theory('equality')], [c_409, c_18])).
% 14.95/6.31  tff(c_6333, plain, (![B_419]: (r1_tarski('#skF_2', B_419))), inference(demodulation, [status(thm), theory('equality')], [c_6276, c_6317])).
% 14.95/6.31  tff(c_6390, plain, (![B_425]: (B_425='#skF_2' | ~r1_tarski(B_425, '#skF_2'))), inference(resolution, [status(thm)], [c_6333, c_2])).
% 14.95/6.31  tff(c_6405, plain, (![B_8]: (k2_relat_1(B_8)='#skF_2' | ~v5_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_20, c_6390])).
% 14.95/6.31  tff(c_8651, plain, (![A_575]: (k2_relat_1(k2_funct_1(A_575))='#skF_2' | ~r1_tarski(k1_relat_1(A_575), '#skF_2') | ~v1_relat_1(k2_funct_1(A_575)) | ~v2_funct_1(A_575) | ~v1_funct_1(A_575) | ~v1_relat_1(A_575))), inference(resolution, [status(thm)], [c_8548, c_6405])).
% 14.95/6.31  tff(c_8654, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7119, c_8651])).
% 14.95/6.31  tff(c_8659, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_8654])).
% 14.95/6.31  tff(c_8951, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8659])).
% 14.95/6.31  tff(c_8954, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_8951])).
% 14.95/6.31  tff(c_8958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_8954])).
% 14.95/6.31  tff(c_8960, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8659])).
% 14.95/6.31  tff(c_418, plain, (![A_94, A_7]: (v5_relat_1(k2_funct_1(A_94), A_7) | ~r1_tarski(k1_relat_1(A_94), A_7) | ~v1_relat_1(k2_funct_1(A_94)) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_409, c_18])).
% 14.95/6.31  tff(c_7126, plain, (![A_26]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_26))) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7119, c_52])).
% 14.95/6.31  tff(c_7170, plain, (![A_486]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_486))))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_6327, c_569, c_7126])).
% 14.95/6.31  tff(c_7197, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_7170])).
% 14.95/6.31  tff(c_7129, plain, (![A_26]: (v1_funct_2('#skF_3', '#skF_1', A_26) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7119, c_54])).
% 14.95/6.31  tff(c_7138, plain, (![A_483]: (v1_funct_2('#skF_3', '#skF_1', A_483))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_6327, c_569, c_7129])).
% 14.95/6.31  tff(c_7142, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_7138, c_72])).
% 14.95/6.31  tff(c_7363, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7197, c_7142])).
% 14.95/6.31  tff(c_7364, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_7363])).
% 14.95/6.31  tff(c_6762, plain, (![B_443, A_444]: (m1_subset_1(B_443, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_443), A_444))) | ~r1_tarski(k2_relat_1(B_443), A_444) | ~v1_funct_1(B_443) | ~v1_relat_1(B_443))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_6787, plain, (![B_443]: (m1_subset_1(B_443, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_443), k1_xboole_0) | ~v1_funct_1(B_443) | ~v1_relat_1(B_443))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6762])).
% 14.95/6.31  tff(c_7439, plain, (![B_495]: (m1_subset_1(B_495, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(B_495), '#skF_1') | ~v1_funct_1(B_495) | ~v1_relat_1(B_495))), inference(demodulation, [status(thm), theory('equality')], [c_7364, c_7364, c_6787])).
% 14.95/6.31  tff(c_9297, plain, (![B_609]: (m1_subset_1(B_609, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(B_609) | ~v5_relat_1(B_609, '#skF_1') | ~v1_relat_1(B_609))), inference(resolution, [status(thm)], [c_20, c_7439])).
% 14.95/6.31  tff(c_7408, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7364, c_7364, c_10])).
% 14.95/6.31  tff(c_7504, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7408, c_150])).
% 14.95/6.31  tff(c_9315, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9297, c_7504])).
% 14.95/6.31  tff(c_9328, plain, (~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8960, c_149, c_9315])).
% 14.95/6.31  tff(c_9363, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_418, c_9328])).
% 14.95/6.31  tff(c_9370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_8960, c_6, c_7119, c_9363])).
% 14.95/6.31  tff(c_9371, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7363])).
% 14.95/6.31  tff(c_6285, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_6276, c_2])).
% 14.95/6.31  tff(c_6297, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_6285])).
% 14.95/6.31  tff(c_9392, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9371, c_6297])).
% 14.95/6.31  tff(c_9421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9392])).
% 14.95/6.31  tff(c_9422, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_7117])).
% 14.95/6.31  tff(c_9442, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9422, c_6297])).
% 14.95/6.31  tff(c_9472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6327, c_9442])).
% 14.95/6.31  tff(c_9473, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6285])).
% 14.95/6.31  tff(c_9499, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9473, c_9473, c_10])).
% 14.95/6.31  tff(c_50, plain, (![B_24, A_23, C_25]: (k1_xboole_0=B_24 | k1_relset_1(A_23, B_24, C_25)=A_23 | ~v1_funct_2(C_25, A_23, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_9936, plain, (![B_646, A_647, C_648]: (B_646='#skF_3' | k1_relset_1(A_647, B_646, C_648)=A_647 | ~v1_funct_2(C_648, A_647, B_646) | ~m1_subset_1(C_648, k1_zfmisc_1(k2_zfmisc_1(A_647, B_646))))), inference(demodulation, [status(thm), theory('equality')], [c_9473, c_50])).
% 14.95/6.31  tff(c_9952, plain, ('#skF_2'='#skF_3' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_9936])).
% 14.95/6.31  tff(c_9958, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_478, c_9952])).
% 14.95/6.31  tff(c_9959, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_9958])).
% 14.95/6.31  tff(c_12351, plain, (![A_783, A_784]: (v5_relat_1(k2_funct_1(A_783), A_784) | ~r1_tarski(k1_relat_1(A_783), A_784) | ~v1_relat_1(k2_funct_1(A_783)) | ~v2_funct_1(A_783) | ~v1_funct_1(A_783) | ~v1_relat_1(A_783))), inference(superposition, [status(thm), theory('equality')], [c_409, c_18])).
% 14.95/6.31  tff(c_258, plain, (![A_67, B_68, A_69]: (v5_relat_1(A_67, B_68) | ~r1_tarski(A_67, k2_zfmisc_1(A_69, B_68)))), inference(resolution, [status(thm)], [c_16, c_235])).
% 14.95/6.31  tff(c_275, plain, (![A_70, B_71]: (v5_relat_1(k2_zfmisc_1(A_70, B_71), B_71))), inference(resolution, [status(thm)], [c_6, c_258])).
% 14.95/6.31  tff(c_278, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_12, c_275])).
% 14.95/6.31  tff(c_9491, plain, (![B_4]: (v5_relat_1('#skF_3', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_9473, c_278])).
% 14.95/6.31  tff(c_597, plain, (![A_7]: (r1_tarski('#skF_2', A_7) | ~v5_relat_1('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_585])).
% 14.95/6.31  tff(c_9654, plain, (![A_620]: (r1_tarski('#skF_2', A_620))), inference(demodulation, [status(thm), theory('equality')], [c_9491, c_597])).
% 14.95/6.31  tff(c_9689, plain, (![A_623]: (A_623='#skF_2' | ~r1_tarski(A_623, '#skF_2'))), inference(resolution, [status(thm)], [c_9654, c_2])).
% 14.95/6.31  tff(c_9704, plain, (![B_8]: (k2_relat_1(B_8)='#skF_2' | ~v5_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_20, c_9689])).
% 14.95/6.31  tff(c_12449, plain, (![A_786]: (k2_relat_1(k2_funct_1(A_786))='#skF_2' | ~r1_tarski(k1_relat_1(A_786), '#skF_2') | ~v1_relat_1(k2_funct_1(A_786)) | ~v2_funct_1(A_786) | ~v1_funct_1(A_786) | ~v1_relat_1(A_786))), inference(resolution, [status(thm)], [c_12351, c_9704])).
% 14.95/6.31  tff(c_12452, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9959, c_12449])).
% 14.95/6.31  tff(c_12457, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_12452])).
% 14.95/6.31  tff(c_12458, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12457])).
% 14.95/6.31  tff(c_12461, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_12458])).
% 14.95/6.31  tff(c_12465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_12461])).
% 14.95/6.31  tff(c_12467, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12457])).
% 14.95/6.31  tff(c_9732, plain, (![B_630, A_631]: (m1_subset_1(B_630, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_630), A_631))) | ~r1_tarski(k2_relat_1(B_630), A_631) | ~v1_funct_1(B_630) | ~v1_relat_1(B_630))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_12871, plain, (![A_808, A_809]: (m1_subset_1(k2_funct_1(A_808), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_808), A_809))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_808)), A_809) | ~v1_funct_1(k2_funct_1(A_808)) | ~v1_relat_1(k2_funct_1(A_808)) | ~v2_funct_1(A_808) | ~v1_funct_1(A_808) | ~v1_relat_1(A_808))), inference(superposition, [status(thm), theory('equality')], [c_28, c_9732])).
% 14.95/6.31  tff(c_12923, plain, (![A_809]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_809))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_809) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_12871])).
% 14.95/6.31  tff(c_12957, plain, (![A_812]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_812))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_812))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_12467, c_149, c_12923])).
% 14.95/6.31  tff(c_12997, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_12957, c_150])).
% 14.95/6.31  tff(c_13001, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_12997])).
% 14.95/6.31  tff(c_13007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_6, c_9959, c_13001])).
% 14.95/6.31  tff(c_13008, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_9958])).
% 14.95/6.31  tff(c_225, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.95/6.31  tff(c_230, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_161, c_225])).
% 14.95/6.31  tff(c_256, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_230])).
% 14.95/6.31  tff(c_13022, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13008, c_256])).
% 14.95/6.31  tff(c_13037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9499, c_13022])).
% 14.95/6.31  tff(c_13038, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_230])).
% 14.95/6.31  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.95/6.31  tff(c_13049, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_13038, c_8])).
% 14.95/6.31  tff(c_13104, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_13049])).
% 14.95/6.31  tff(c_13041, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13038, c_64])).
% 14.95/6.31  tff(c_13464, plain, (![A_873, B_874, C_875]: (k1_relset_1(A_873, B_874, C_875)=k1_relat_1(C_875) | ~m1_subset_1(C_875, k1_zfmisc_1(k2_zfmisc_1(A_873, B_874))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_13498, plain, (![C_878]: (k1_relset_1('#skF_1', '#skF_2', C_878)=k1_relat_1(C_878) | ~m1_subset_1(C_878, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13038, c_13464])).
% 14.95/6.31  tff(c_13506, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13041, c_13498])).
% 14.95/6.31  tff(c_14147, plain, (![B_944, C_945, A_946]: (k1_xboole_0=B_944 | v1_funct_2(C_945, A_946, B_944) | k1_relset_1(A_946, B_944, C_945)!=A_946 | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(A_946, B_944))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_14153, plain, (![C_945]: (k1_xboole_0='#skF_2' | v1_funct_2(C_945, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_945)!='#skF_1' | ~m1_subset_1(C_945, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13038, c_14147])).
% 14.95/6.31  tff(c_14241, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_14153])).
% 14.95/6.31  tff(c_13550, plain, (![A_884, B_885, C_886]: (k2_relset_1(A_884, B_885, C_886)=k2_relat_1(C_886) | ~m1_subset_1(C_886, k1_zfmisc_1(k2_zfmisc_1(A_884, B_885))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_13587, plain, (![C_890]: (k2_relset_1('#skF_1', '#skF_2', C_890)=k2_relat_1(C_890) | ~m1_subset_1(C_890, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13038, c_13550])).
% 14.95/6.31  tff(c_13590, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_13041, c_13587])).
% 14.95/6.31  tff(c_13596, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_13590])).
% 14.95/6.31  tff(c_13622, plain, (![A_7]: (v5_relat_1('#skF_3', A_7) | ~r1_tarski('#skF_2', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13596, c_18])).
% 14.95/6.31  tff(c_13673, plain, (![A_894]: (v5_relat_1('#skF_3', A_894) | ~r1_tarski('#skF_2', A_894))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_13622])).
% 14.95/6.31  tff(c_13073, plain, (![B_814, A_815]: (r1_tarski(k2_relat_1(B_814), A_815) | ~v5_relat_1(B_814, A_815) | ~v1_relat_1(B_814))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_13091, plain, (![B_814]: (v1_relat_1(k2_relat_1(B_814)) | ~v5_relat_1(B_814, k1_xboole_0) | ~v1_relat_1(B_814))), inference(resolution, [status(thm)], [c_13073, c_185])).
% 14.95/6.31  tff(c_13613, plain, (v1_relat_1('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13596, c_13091])).
% 14.95/6.31  tff(c_13637, plain, (v1_relat_1('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_13613])).
% 14.95/6.31  tff(c_13648, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_13637])).
% 14.95/6.31  tff(c_13688, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_13673, c_13648])).
% 14.95/6.31  tff(c_14267, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14241, c_13688])).
% 14.95/6.31  tff(c_14308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14267])).
% 14.95/6.31  tff(c_14310, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_14153])).
% 14.95/6.31  tff(c_14219, plain, (![B_960, A_961, C_962]: (k1_xboole_0=B_960 | k1_relset_1(A_961, B_960, C_962)=A_961 | ~v1_funct_2(C_962, A_961, B_960) | ~m1_subset_1(C_962, k1_zfmisc_1(k2_zfmisc_1(A_961, B_960))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_14225, plain, (![C_962]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_962)='#skF_1' | ~v1_funct_2(C_962, '#skF_1', '#skF_2') | ~m1_subset_1(C_962, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13038, c_14219])).
% 14.95/6.31  tff(c_14421, plain, (![C_981]: (k1_relset_1('#skF_1', '#skF_2', C_981)='#skF_1' | ~v1_funct_2(C_981, '#skF_1', '#skF_2') | ~m1_subset_1(C_981, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_14310, c_14225])).
% 14.95/6.31  tff(c_14424, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13041, c_14421])).
% 14.95/6.31  tff(c_14431, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13506, c_14424])).
% 14.95/6.31  tff(c_13299, plain, (![A_854]: (k2_relat_1(k2_funct_1(A_854))=k1_relat_1(A_854) | ~v2_funct_1(A_854) | ~v1_funct_1(A_854) | ~v1_relat_1(A_854))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_13148, plain, (![B_826, A_827]: (v5_relat_1(B_826, A_827) | ~r1_tarski(k2_relat_1(B_826), A_827) | ~v1_relat_1(B_826))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_13157, plain, (![B_826]: (v5_relat_1(B_826, k2_relat_1(B_826)) | ~v1_relat_1(B_826))), inference(resolution, [status(thm)], [c_6, c_13148])).
% 14.95/6.31  tff(c_16092, plain, (![A_1064]: (v5_relat_1(k2_funct_1(A_1064), k1_relat_1(A_1064)) | ~v1_relat_1(k2_funct_1(A_1064)) | ~v2_funct_1(A_1064) | ~v1_funct_1(A_1064) | ~v1_relat_1(A_1064))), inference(superposition, [status(thm), theory('equality')], [c_13299, c_13157])).
% 14.95/6.31  tff(c_16095, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14431, c_16092])).
% 14.95/6.31  tff(c_16100, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_16095])).
% 14.95/6.31  tff(c_16101, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_16100])).
% 14.95/6.31  tff(c_16104, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_16101])).
% 14.95/6.31  tff(c_16108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_16104])).
% 14.95/6.31  tff(c_16110, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_16100])).
% 14.95/6.31  tff(c_16109, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_16100])).
% 14.95/6.31  tff(c_16449, plain, (![A_1092, A_1093]: (r1_tarski(k1_relat_1(A_1092), A_1093) | ~v5_relat_1(k2_funct_1(A_1092), A_1093) | ~v1_relat_1(k2_funct_1(A_1092)) | ~v2_funct_1(A_1092) | ~v1_funct_1(A_1092) | ~v1_relat_1(A_1092))), inference(superposition, [status(thm), theory('equality')], [c_13299, c_20])).
% 14.95/6.31  tff(c_17180, plain, (![A_1112]: (r1_tarski(k1_relat_1(A_1112), k2_relat_1(k2_funct_1(A_1112))) | ~v2_funct_1(A_1112) | ~v1_funct_1(A_1112) | ~v1_relat_1(A_1112) | ~v1_relat_1(k2_funct_1(A_1112)))), inference(resolution, [status(thm)], [c_13157, c_16449])).
% 14.95/6.31  tff(c_17188, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14431, c_17180])).
% 14.95/6.31  tff(c_17198, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16110, c_179, c_68, c_62, c_17188])).
% 14.95/6.31  tff(c_13089, plain, (![B_814, A_815]: (k2_relat_1(B_814)=A_815 | ~r1_tarski(A_815, k2_relat_1(B_814)) | ~v5_relat_1(B_814, A_815) | ~v1_relat_1(B_814))), inference(resolution, [status(thm)], [c_13073, c_2])).
% 14.95/6.31  tff(c_17202, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17198, c_13089])).
% 14.95/6.31  tff(c_17210, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16110, c_16109, c_17202])).
% 14.95/6.31  tff(c_13899, plain, (![B_926, A_927]: (m1_subset_1(B_926, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_926), A_927))) | ~r1_tarski(k2_relat_1(B_926), A_927) | ~v1_funct_1(B_926) | ~v1_relat_1(B_926))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_17662, plain, (![A_1119, A_1120]: (m1_subset_1(k2_funct_1(A_1119), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1119), A_1120))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1119)), A_1120) | ~v1_funct_1(k2_funct_1(A_1119)) | ~v1_relat_1(k2_funct_1(A_1119)) | ~v2_funct_1(A_1119) | ~v1_funct_1(A_1119) | ~v1_relat_1(A_1119))), inference(superposition, [status(thm), theory('equality')], [c_28, c_13899])).
% 14.95/6.31  tff(c_17692, plain, (![A_1120]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_1120))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1120) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13596, c_17662])).
% 14.95/6.31  tff(c_17712, plain, (![A_1121]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_1121))) | ~r1_tarski('#skF_1', A_1121))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_16110, c_149, c_17210, c_17692])).
% 14.95/6.31  tff(c_17736, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_17712, c_150])).
% 14.95/6.31  tff(c_17756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_17736])).
% 14.95/6.31  tff(c_17758, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_13637])).
% 14.95/6.31  tff(c_13625, plain, (![A_7]: (r1_tarski('#skF_2', A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13596, c_20])).
% 14.95/6.31  tff(c_17781, plain, (![A_1124]: (r1_tarski('#skF_2', A_1124) | ~v5_relat_1('#skF_3', A_1124))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_13625])).
% 14.95/6.31  tff(c_17804, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_17758, c_17781])).
% 14.95/6.31  tff(c_18167, plain, (![B_1162, A_1163, C_1164]: (k1_xboole_0=B_1162 | k1_relset_1(A_1163, B_1162, C_1164)=A_1163 | ~v1_funct_2(C_1164, A_1163, B_1162) | ~m1_subset_1(C_1164, k1_zfmisc_1(k2_zfmisc_1(A_1163, B_1162))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_18173, plain, (![C_1164]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1164)='#skF_1' | ~v1_funct_2(C_1164, '#skF_1', '#skF_2') | ~m1_subset_1(C_1164, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13038, c_18167])).
% 14.95/6.31  tff(c_18201, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_18173])).
% 14.95/6.31  tff(c_17819, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_17804, c_2])).
% 14.95/6.31  tff(c_17822, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_17819])).
% 14.95/6.31  tff(c_18218, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18201, c_17822])).
% 14.95/6.31  tff(c_18260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_18218])).
% 14.95/6.31  tff(c_18353, plain, (![C_1179]: (k1_relset_1('#skF_1', '#skF_2', C_1179)='#skF_1' | ~v1_funct_2(C_1179, '#skF_1', '#skF_2') | ~m1_subset_1(C_1179, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_18173])).
% 14.95/6.31  tff(c_18356, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13041, c_18353])).
% 14.95/6.31  tff(c_18363, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13506, c_18356])).
% 14.95/6.31  tff(c_18372, plain, (![A_26]: (v1_funct_2('#skF_3', '#skF_1', A_26) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18363, c_54])).
% 14.95/6.31  tff(c_18384, plain, (![A_1180]: (v1_funct_2('#skF_3', '#skF_1', A_1180) | ~r1_tarski('#skF_2', A_1180))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_13596, c_18372])).
% 14.95/6.31  tff(c_18387, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_18384, c_72])).
% 14.95/6.31  tff(c_18390, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_17804, c_18387])).
% 14.95/6.31  tff(c_18391, plain, (k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_13104, c_18390])).
% 14.95/6.31  tff(c_18392, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_18391])).
% 14.95/6.31  tff(c_18369, plain, (![A_26]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_26))) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18363, c_52])).
% 14.95/6.31  tff(c_18417, plain, (![A_1184]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_1184))) | ~r1_tarski('#skF_2', A_1184))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_13596, c_18369])).
% 14.95/6.31  tff(c_18448, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_18417])).
% 14.95/6.31  tff(c_18464, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_17804, c_18448])).
% 14.95/6.31  tff(c_18466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18392, c_18464])).
% 14.95/6.31  tff(c_18467, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18391])).
% 14.95/6.31  tff(c_13273, plain, (![B_851, A_852, B_853]: (v1_relat_1(k2_relat_1(B_851)) | ~v5_relat_1(B_851, k2_zfmisc_1(A_852, B_853)) | ~v1_relat_1(B_851))), inference(resolution, [status(thm)], [c_13073, c_178])).
% 14.95/6.31  tff(c_13298, plain, (![A_5]: (v1_relat_1(k2_relat_1(A_5)) | ~v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_255, c_13273])).
% 14.95/6.31  tff(c_13610, plain, (v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13596, c_13298])).
% 14.95/6.31  tff(c_13635, plain, (v1_relat_1('#skF_2') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_179, c_13610])).
% 14.95/6.31  tff(c_13647, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_13635])).
% 14.95/6.31  tff(c_18495, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18467, c_13647])).
% 14.95/6.31  tff(c_18468, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_18391])).
% 14.95/6.31  tff(c_18620, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18467, c_18468])).
% 14.95/6.31  tff(c_18623, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_18620, c_14])).
% 14.95/6.31  tff(c_18627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18495, c_18623])).
% 14.95/6.31  tff(c_18628, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17819])).
% 14.95/6.31  tff(c_18668, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18628, c_13104])).
% 14.95/6.31  tff(c_18707, plain, (![A_1198]: (k2_zfmisc_1(A_1198, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18628, c_18628, c_10])).
% 14.95/6.31  tff(c_18741, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18707, c_13038])).
% 14.95/6.31  tff(c_18761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18668, c_18741])).
% 14.95/6.31  tff(c_18763, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_13635])).
% 14.95/6.31  tff(c_18837, plain, (![A_1205]: (r1_tarski('#skF_2', A_1205) | ~v5_relat_1('#skF_3', A_1205))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_13625])).
% 14.95/6.31  tff(c_18849, plain, (![B_64]: (r1_tarski('#skF_2', B_64) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_255, c_18837])).
% 14.95/6.31  tff(c_18861, plain, (![B_64]: (r1_tarski('#skF_2', B_64))), inference(demodulation, [status(thm), theory('equality')], [c_18763, c_18849])).
% 14.95/6.31  tff(c_19580, plain, (![B_1227, A_1228, C_1229]: (k1_xboole_0=B_1227 | k1_relset_1(A_1228, B_1227, C_1229)=A_1228 | ~v1_funct_2(C_1229, A_1228, B_1227) | ~m1_subset_1(C_1229, k1_zfmisc_1(k2_zfmisc_1(A_1228, B_1227))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_19586, plain, (![C_1229]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1229)='#skF_1' | ~v1_funct_2(C_1229, '#skF_1', '#skF_2') | ~m1_subset_1(C_1229, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_13038, c_19580])).
% 14.95/6.31  tff(c_19628, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_19586])).
% 14.95/6.31  tff(c_18766, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_18763, c_2])).
% 14.95/6.31  tff(c_18772, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_13104, c_18766])).
% 14.95/6.31  tff(c_19634, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19628, c_18772])).
% 14.95/6.31  tff(c_19660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18861, c_19634])).
% 14.95/6.31  tff(c_19757, plain, (![C_1237]: (k1_relset_1('#skF_1', '#skF_2', C_1237)='#skF_1' | ~v1_funct_2(C_1237, '#skF_1', '#skF_2') | ~m1_subset_1(C_1237, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_19586])).
% 14.95/6.31  tff(c_19760, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13041, c_19757])).
% 14.95/6.31  tff(c_19767, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_13506, c_19760])).
% 14.95/6.31  tff(c_19773, plain, (![A_26]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_26))) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_19767, c_52])).
% 14.95/6.31  tff(c_19796, plain, (![A_1239]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_1239))))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_18861, c_13596, c_19773])).
% 14.95/6.31  tff(c_19825, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_19796])).
% 14.95/6.31  tff(c_19776, plain, (![A_26]: (v1_funct_2('#skF_3', '#skF_1', A_26) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_19767, c_54])).
% 14.95/6.31  tff(c_19785, plain, (![A_1238]: (v1_funct_2('#skF_3', '#skF_1', A_1238))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_18861, c_13596, c_19776])).
% 14.95/6.31  tff(c_19788, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_19785, c_72])).
% 14.95/6.31  tff(c_19791, plain, (k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_13104, c_19788])).
% 14.95/6.31  tff(c_19952, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19825, c_19791])).
% 14.95/6.31  tff(c_19977, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19952, c_13104])).
% 14.95/6.31  tff(c_19984, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_19952, c_19952, c_12])).
% 14.95/6.31  tff(c_20118, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19984, c_13038])).
% 14.95/6.31  tff(c_20122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19977, c_20118])).
% 14.95/6.31  tff(c_20124, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_13049])).
% 14.95/6.31  tff(c_20142, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20124, c_20124, c_12])).
% 14.95/6.31  tff(c_20123, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_13049])).
% 14.95/6.31  tff(c_20149, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20124, c_20124, c_20123])).
% 14.95/6.31  tff(c_20150, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_20149])).
% 14.95/6.31  tff(c_20155, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20150, c_150])).
% 14.95/6.31  tff(c_20257, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20142, c_20155])).
% 14.95/6.31  tff(c_20143, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20124, c_20124, c_10])).
% 14.95/6.31  tff(c_21246, plain, (![B_1381, A_1382]: (m1_subset_1(B_1381, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1381), A_1382))) | ~r1_tarski(k2_relat_1(B_1381), A_1382) | ~v1_funct_1(B_1381) | ~v1_relat_1(B_1381))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_21490, plain, (![B_1410]: (m1_subset_1(B_1410, k1_zfmisc_1('#skF_3')) | ~r1_tarski(k2_relat_1(B_1410), '#skF_3') | ~v1_funct_1(B_1410) | ~v1_relat_1(B_1410))), inference(superposition, [status(thm), theory('equality')], [c_20143, c_21246])).
% 14.95/6.31  tff(c_21509, plain, (![B_1411]: (m1_subset_1(B_1411, k1_zfmisc_1('#skF_3')) | ~v1_funct_1(B_1411) | ~v5_relat_1(B_1411, '#skF_3') | ~v1_relat_1(B_1411))), inference(resolution, [status(thm)], [c_20, c_21490])).
% 14.95/6.31  tff(c_21524, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_21509, c_20257])).
% 14.95/6.31  tff(c_21541, plain, (~v5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_21524])).
% 14.95/6.31  tff(c_21545, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_21541])).
% 14.95/6.31  tff(c_21548, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_21545])).
% 14.95/6.31  tff(c_21552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_21548])).
% 14.95/6.31  tff(c_21554, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_21541])).
% 14.95/6.31  tff(c_20652, plain, (![A_1330, B_1331, C_1332]: (k2_relset_1(A_1330, B_1331, C_1332)=k2_relat_1(C_1332) | ~m1_subset_1(C_1332, k1_zfmisc_1(k2_zfmisc_1(A_1330, B_1331))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_20833, plain, (![A_1361, C_1362]: (k2_relset_1(A_1361, '#skF_3', C_1362)=k2_relat_1(C_1362) | ~m1_subset_1(C_1362, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20143, c_20652])).
% 14.95/6.31  tff(c_20849, plain, (![A_1365]: (k2_relset_1(A_1365, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_13041, c_20833])).
% 14.95/6.31  tff(c_20156, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20150, c_20150, c_60])).
% 14.95/6.31  tff(c_20856, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_20849, c_20156])).
% 14.95/6.31  tff(c_24914, plain, (![A_1527, A_1528]: (m1_subset_1(k2_funct_1(A_1527), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1527), A_1528))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_1527)), A_1528) | ~v1_funct_1(k2_funct_1(A_1527)) | ~v1_relat_1(k2_funct_1(A_1527)) | ~v2_funct_1(A_1527) | ~v1_funct_1(A_1527) | ~v1_relat_1(A_1527))), inference(superposition, [status(thm), theory('equality')], [c_28, c_21246])).
% 14.95/6.31  tff(c_24959, plain, (![A_1528]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_1528))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1528) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20856, c_24914])).
% 14.95/6.31  tff(c_24984, plain, (![A_1528]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1528))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_68, c_62, c_21554, c_149, c_20142, c_24959])).
% 14.95/6.31  tff(c_24986, plain, (![A_1529]: (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_1529))), inference(negUnitSimplification, [status(thm)], [c_20257, c_24984])).
% 14.95/6.31  tff(c_25015, plain, $false, inference(resolution, [status(thm)], [c_6, c_24986])).
% 14.95/6.31  tff(c_25016, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_20149])).
% 14.95/6.31  tff(c_25026, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_179])).
% 14.95/6.31  tff(c_25032, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_68])).
% 14.95/6.31  tff(c_25031, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_62])).
% 14.95/6.31  tff(c_25028, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_149])).
% 14.95/6.31  tff(c_25057, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_25016, c_20143])).
% 14.95/6.31  tff(c_25977, plain, (![B_1652, A_1653]: (m1_subset_1(B_1652, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1652), A_1653))) | ~r1_tarski(k2_relat_1(B_1652), A_1653) | ~v1_funct_1(B_1652) | ~v1_relat_1(B_1652))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_27783, plain, (![B_1745]: (m1_subset_1(B_1745, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(B_1745), '#skF_1') | ~v1_funct_1(B_1745) | ~v1_relat_1(B_1745))), inference(superposition, [status(thm), theory('equality')], [c_25057, c_25977])).
% 14.95/6.31  tff(c_27905, plain, (![B_1751]: (m1_subset_1(B_1751, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(B_1751) | ~v5_relat_1(B_1751, '#skF_1') | ~v1_relat_1(B_1751))), inference(resolution, [status(thm)], [c_20, c_27783])).
% 14.95/6.31  tff(c_25027, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_150])).
% 14.95/6.31  tff(c_25147, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25057, c_25027])).
% 14.95/6.31  tff(c_27925, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v5_relat_1(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_27905, c_25147])).
% 14.95/6.31  tff(c_27939, plain, (~v5_relat_1(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25028, c_27925])).
% 14.95/6.31  tff(c_27941, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_27939])).
% 14.95/6.31  tff(c_27944, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_27941])).
% 14.95/6.31  tff(c_27948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25026, c_25032, c_27944])).
% 14.95/6.31  tff(c_27950, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_27939])).
% 14.95/6.31  tff(c_25022, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_25016, c_13041])).
% 14.95/6.31  tff(c_25093, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_25016, c_20142])).
% 14.95/6.31  tff(c_25540, plain, (![A_1603, B_1604, C_1605]: (k1_relset_1(A_1603, B_1604, C_1605)=k1_relat_1(C_1605) | ~m1_subset_1(C_1605, k1_zfmisc_1(k2_zfmisc_1(A_1603, B_1604))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_25759, plain, (![B_1638, C_1639]: (k1_relset_1('#skF_1', B_1638, C_1639)=k1_relat_1(C_1639) | ~m1_subset_1(C_1639, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_25093, c_25540])).
% 14.95/6.31  tff(c_25767, plain, (![B_1640]: (k1_relset_1('#skF_1', B_1640, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_25022, c_25759])).
% 14.95/6.31  tff(c_25030, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_66])).
% 14.95/6.31  tff(c_25018, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25016, c_20124])).
% 14.95/6.31  tff(c_48, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_69, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_48])).
% 14.95/6.31  tff(c_25646, plain, (![B_1617, C_1618]: (k1_relset_1('#skF_1', B_1617, C_1618)='#skF_1' | ~v1_funct_2(C_1618, '#skF_1', B_1617) | ~m1_subset_1(C_1618, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_25018, c_25018, c_25018, c_25018, c_69])).
% 14.95/6.31  tff(c_25651, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_25030, c_25646])).
% 14.95/6.31  tff(c_25658, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25022, c_25651])).
% 14.95/6.31  tff(c_25774, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_25767, c_25658])).
% 14.95/6.31  tff(c_25252, plain, (![A_1560]: (k2_relat_1(k2_funct_1(A_1560))=k1_relat_1(A_1560) | ~v2_funct_1(A_1560) | ~v1_funct_1(A_1560) | ~v1_relat_1(A_1560))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_25264, plain, (![A_1560, A_7]: (v5_relat_1(k2_funct_1(A_1560), A_7) | ~r1_tarski(k1_relat_1(A_1560), A_7) | ~v1_relat_1(k2_funct_1(A_1560)) | ~v2_funct_1(A_1560) | ~v1_funct_1(A_1560) | ~v1_relat_1(A_1560))), inference(superposition, [status(thm), theory('equality')], [c_25252, c_18])).
% 14.95/6.31  tff(c_27949, plain, (~v5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_27939])).
% 14.95/6.31  tff(c_27953, plain, (~r1_tarski(k1_relat_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_25264, c_27949])).
% 14.95/6.31  tff(c_27960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25026, c_25032, c_25031, c_27950, c_6, c_25774, c_27953])).
% 14.95/6.31  tff(c_27961, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_148])).
% 14.95/6.31  tff(c_28376, plain, (![A_1824, B_1825, C_1826]: (k2_relset_1(A_1824, B_1825, C_1826)=k2_relat_1(C_1826) | ~m1_subset_1(C_1826, k1_zfmisc_1(k2_zfmisc_1(A_1824, B_1825))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_28386, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_28376])).
% 14.95/6.31  tff(c_28396, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28386])).
% 14.95/6.31  tff(c_27962, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_148])).
% 14.95/6.31  tff(c_28323, plain, (![A_1816, B_1817, C_1818]: (k1_relset_1(A_1816, B_1817, C_1818)=k1_relat_1(C_1818) | ~m1_subset_1(C_1818, k1_zfmisc_1(k2_zfmisc_1(A_1816, B_1817))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_28340, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_27962, c_28323])).
% 14.95/6.31  tff(c_28782, plain, (![B_1870, C_1871, A_1872]: (k1_xboole_0=B_1870 | v1_funct_2(C_1871, A_1872, B_1870) | k1_relset_1(A_1872, B_1870, C_1871)!=A_1872 | ~m1_subset_1(C_1871, k1_zfmisc_1(k2_zfmisc_1(A_1872, B_1870))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_28788, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_27962, c_28782])).
% 14.95/6.31  tff(c_28804, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28340, c_28788])).
% 14.95/6.31  tff(c_28805, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27961, c_28804])).
% 14.95/6.31  tff(c_28810, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_28805])).
% 14.95/6.31  tff(c_28813, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_28810])).
% 14.95/6.31  tff(c_28816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_28396, c_28813])).
% 14.95/6.31  tff(c_28817, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_28805])).
% 14.95/6.31  tff(c_28080, plain, (![C_1773, B_1774, A_1775]: (v5_relat_1(C_1773, B_1774) | ~m1_subset_1(C_1773, k1_zfmisc_1(k2_zfmisc_1(A_1775, B_1774))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.95/6.31  tff(c_28115, plain, (![C_1780, B_1781]: (v5_relat_1(C_1780, B_1781) | ~m1_subset_1(C_1780, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_28080])).
% 14.95/6.31  tff(c_28119, plain, (![A_5, B_1781]: (v5_relat_1(A_5, B_1781) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_28115])).
% 14.95/6.31  tff(c_28120, plain, (![B_1782, A_1783]: (r1_tarski(k2_relat_1(B_1782), A_1783) | ~v5_relat_1(B_1782, A_1783) | ~v1_relat_1(B_1782))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_27994, plain, (![A_5, A_1757, B_1758]: (v1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_1757, B_1758)))), inference(resolution, [status(thm)], [c_16, c_27978])).
% 14.95/6.31  tff(c_28275, plain, (![B_1808, A_1809, B_1810]: (v1_relat_1(k2_relat_1(B_1808)) | ~v5_relat_1(B_1808, k2_zfmisc_1(A_1809, B_1810)) | ~v1_relat_1(B_1808))), inference(resolution, [status(thm)], [c_28120, c_27994])).
% 14.95/6.31  tff(c_28298, plain, (![A_5]: (v1_relat_1(k2_relat_1(A_5)) | ~v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_28119, c_28275])).
% 14.95/6.31  tff(c_28400, plain, (v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28396, c_28298])).
% 14.95/6.31  tff(c_28416, plain, (v1_relat_1('#skF_2') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_28400])).
% 14.95/6.31  tff(c_28426, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_28416])).
% 14.95/6.31  tff(c_28839, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28817, c_28426])).
% 14.95/6.31  tff(c_28858, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28817, c_28817, c_12])).
% 14.95/6.31  tff(c_27965, plain, (![A_1754, B_1755]: (r1_tarski(A_1754, B_1755) | ~m1_subset_1(A_1754, k1_zfmisc_1(B_1755)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.95/6.31  tff(c_27973, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_27965])).
% 14.95/6.31  tff(c_29025, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28858, c_27973])).
% 14.95/6.31  tff(c_29028, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28839, c_29025])).
% 14.95/6.31  tff(c_29030, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_28416])).
% 14.95/6.31  tff(c_28412, plain, (![A_7]: (r1_tarski('#skF_2', A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28396, c_20])).
% 14.95/6.31  tff(c_29063, plain, (![A_1882]: (r1_tarski('#skF_2', A_1882) | ~v5_relat_1('#skF_3', A_1882))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_28412])).
% 14.95/6.31  tff(c_29074, plain, (![B_1781]: (r1_tarski('#skF_2', B_1781) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_28119, c_29063])).
% 14.95/6.31  tff(c_29084, plain, (![B_1781]: (r1_tarski('#skF_2', B_1781))), inference(demodulation, [status(thm), theory('equality')], [c_29030, c_29074])).
% 14.95/6.31  tff(c_28342, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_28323])).
% 14.95/6.31  tff(c_29971, plain, (![B_1951, A_1952, C_1953]: (k1_xboole_0=B_1951 | k1_relset_1(A_1952, B_1951, C_1953)=A_1952 | ~v1_funct_2(C_1953, A_1952, B_1951) | ~m1_subset_1(C_1953, k1_zfmisc_1(k2_zfmisc_1(A_1952, B_1951))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_29984, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_29971])).
% 14.95/6.31  tff(c_29997, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28342, c_29984])).
% 14.95/6.31  tff(c_29999, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_29997])).
% 14.95/6.31  tff(c_27993, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_27962, c_27978])).
% 14.95/6.31  tff(c_30128, plain, (![B_1959, C_1960, A_1961]: (k1_xboole_0=B_1959 | v1_funct_2(C_1960, A_1961, B_1959) | k1_relset_1(A_1961, B_1959, C_1960)!=A_1961 | ~m1_subset_1(C_1960, k1_zfmisc_1(k2_zfmisc_1(A_1961, B_1959))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_30137, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_27962, c_30128])).
% 14.95/6.31  tff(c_30152, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28340, c_30137])).
% 14.95/6.31  tff(c_30153, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27961, c_30152])).
% 14.95/6.31  tff(c_30222, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_30153])).
% 14.95/6.31  tff(c_30225, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_30222])).
% 14.95/6.31  tff(c_30228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_28396, c_30225])).
% 14.95/6.31  tff(c_30229, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_30153])).
% 14.95/6.31  tff(c_30274, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30229, c_30229, c_10])).
% 14.95/6.31  tff(c_30457, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30274, c_27962])).
% 14.95/6.31  tff(c_28093, plain, (![C_1773, B_4]: (v5_relat_1(C_1773, B_4) | ~m1_subset_1(C_1773, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_28080])).
% 14.95/6.31  tff(c_30724, plain, (![C_1985, B_1986]: (v5_relat_1(C_1985, B_1986) | ~m1_subset_1(C_1985, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30229, c_28093])).
% 14.95/6.31  tff(c_30741, plain, (![B_1987]: (v5_relat_1(k2_funct_1('#skF_3'), B_1987))), inference(resolution, [status(thm)], [c_30457, c_30724])).
% 14.95/6.31  tff(c_29090, plain, (![B_1883]: (r1_tarski('#skF_2', B_1883))), inference(demodulation, [status(thm), theory('equality')], [c_29030, c_29074])).
% 14.95/6.31  tff(c_29138, plain, (![B_1887]: (B_1887='#skF_2' | ~r1_tarski(B_1887, '#skF_2'))), inference(resolution, [status(thm)], [c_29090, c_2])).
% 14.95/6.31  tff(c_29153, plain, (![B_8]: (k2_relat_1(B_8)='#skF_2' | ~v5_relat_1(B_8, '#skF_2') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_20, c_29138])).
% 14.95/6.31  tff(c_30748, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_30741, c_29153])).
% 14.95/6.31  tff(c_30758, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27993, c_30748])).
% 14.95/6.31  tff(c_30773, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30758, c_26])).
% 14.95/6.31  tff(c_30789, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_29999, c_30773])).
% 14.95/6.31  tff(c_30823, plain, (![B_1781]: (r1_tarski('#skF_1', B_1781))), inference(demodulation, [status(thm), theory('equality')], [c_30789, c_29084])).
% 14.95/6.31  tff(c_27977, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_27962, c_14])).
% 14.95/6.31  tff(c_28008, plain, (![B_1761, A_1762]: (B_1761=A_1762 | ~r1_tarski(B_1761, A_1762) | ~r1_tarski(A_1762, B_1761))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.95/6.31  tff(c_28015, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_27977, c_28008])).
% 14.95/6.31  tff(c_28106, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_28015])).
% 14.95/6.31  tff(c_30455, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30274, c_28106])).
% 14.95/6.31  tff(c_30875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30823, c_30455])).
% 14.95/6.31  tff(c_30876, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_29997])).
% 14.95/6.31  tff(c_29043, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_29030, c_2])).
% 14.95/6.31  tff(c_29047, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_29043])).
% 14.95/6.31  tff(c_30899, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30876, c_29047])).
% 14.95/6.31  tff(c_30926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29084, c_30899])).
% 14.95/6.31  tff(c_30927, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_29043])).
% 14.95/6.31  tff(c_46, plain, (![B_24, C_25, A_23]: (k1_xboole_0=B_24 | v1_funct_2(C_25, A_23, B_24) | k1_relset_1(A_23, B_24, C_25)!=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_31935, plain, (![B_2057, C_2058, A_2059]: (B_2057='#skF_3' | v1_funct_2(C_2058, A_2059, B_2057) | k1_relset_1(A_2059, B_2057, C_2058)!=A_2059 | ~m1_subset_1(C_2058, k1_zfmisc_1(k2_zfmisc_1(A_2059, B_2057))))), inference(demodulation, [status(thm), theory('equality')], [c_30927, c_46])).
% 14.95/6.31  tff(c_31947, plain, ('#skF_3'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_27962, c_31935])).
% 14.95/6.31  tff(c_31958, plain, ('#skF_3'='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28340, c_31947])).
% 14.95/6.31  tff(c_31959, plain, ('#skF_3'='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27961, c_31958])).
% 14.95/6.31  tff(c_31963, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_31959])).
% 14.95/6.31  tff(c_31966, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_31963])).
% 14.95/6.31  tff(c_31969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_28396, c_31966])).
% 14.95/6.31  tff(c_31970, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_31959])).
% 14.95/6.31  tff(c_30948, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30927, c_30927, c_12])).
% 14.95/6.31  tff(c_31996, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31970, c_31970, c_30948])).
% 14.95/6.31  tff(c_28016, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_27973, c_28008])).
% 14.95/6.31  tff(c_28048, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_28016])).
% 14.95/6.31  tff(c_32006, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_31970, c_28048])).
% 14.95/6.31  tff(c_32286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_31996, c_32006])).
% 14.95/6.31  tff(c_32287, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_28015])).
% 14.95/6.31  tff(c_32290, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32287, c_27962])).
% 14.95/6.31  tff(c_32794, plain, (![A_2141, B_2142, C_2143]: (k1_relset_1(A_2141, B_2142, C_2143)=k1_relat_1(C_2143) | ~m1_subset_1(C_2143, k1_zfmisc_1(k2_zfmisc_1(A_2141, B_2142))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_36333, plain, (![C_2367]: (k1_relset_1('#skF_2', '#skF_1', C_2367)=k1_relat_1(C_2367) | ~m1_subset_1(C_2367, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_32287, c_32794])).
% 14.95/6.31  tff(c_36341, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_32290, c_36333])).
% 14.95/6.31  tff(c_34596, plain, (![B_2282, C_2283, A_2284]: (k1_xboole_0=B_2282 | v1_funct_2(C_2283, A_2284, B_2282) | k1_relset_1(A_2284, B_2282, C_2283)!=A_2284 | ~m1_subset_1(C_2283, k1_zfmisc_1(k2_zfmisc_1(A_2284, B_2282))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_34602, plain, (![C_2283]: (k1_xboole_0='#skF_1' | v1_funct_2(C_2283, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2283)!='#skF_2' | ~m1_subset_1(C_2283, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_32287, c_34596])).
% 14.95/6.31  tff(c_34658, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_34602])).
% 14.95/6.31  tff(c_32301, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_32287, c_8])).
% 14.95/6.31  tff(c_32356, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32301])).
% 14.95/6.31  tff(c_34694, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34658, c_32356])).
% 14.95/6.31  tff(c_34704, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34658, c_34658, c_10])).
% 14.95/6.31  tff(c_34798, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34704, c_32287])).
% 14.95/6.31  tff(c_34800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34694, c_34798])).
% 14.95/6.31  tff(c_34802, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_34602])).
% 14.95/6.31  tff(c_33087, plain, (![C_2159]: (k1_relset_1('#skF_2', '#skF_1', C_2159)=k1_relat_1(C_2159) | ~m1_subset_1(C_2159, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_32287, c_32794])).
% 14.95/6.31  tff(c_33095, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_32290, c_33087])).
% 14.95/6.31  tff(c_33395, plain, (![B_2183, C_2184, A_2185]: (k1_xboole_0=B_2183 | v1_funct_2(C_2184, A_2185, B_2183) | k1_relset_1(A_2185, B_2183, C_2184)!=A_2185 | ~m1_subset_1(C_2184, k1_zfmisc_1(k2_zfmisc_1(A_2185, B_2183))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_33401, plain, (![C_2184]: (k1_xboole_0='#skF_1' | v1_funct_2(C_2184, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2184)!='#skF_2' | ~m1_subset_1(C_2184, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_32287, c_33395])).
% 14.95/6.31  tff(c_33445, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_33401])).
% 14.95/6.31  tff(c_32339, plain, (![C_2082, B_2083]: (v5_relat_1(C_2082, B_2083) | ~m1_subset_1(C_2082, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_28080])).
% 14.95/6.31  tff(c_32343, plain, (![A_5, B_2083]: (v5_relat_1(A_5, B_2083) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_32339])).
% 14.95/6.31  tff(c_32388, plain, (![B_2092, A_2093]: (r1_tarski(k2_relat_1(B_2092), A_2093) | ~v5_relat_1(B_2092, A_2093) | ~v1_relat_1(B_2092))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.95/6.31  tff(c_27996, plain, (![C_1759]: (v1_relat_1(C_1759) | ~m1_subset_1(C_1759, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_27978])).
% 14.95/6.31  tff(c_28001, plain, (![A_5]: (v1_relat_1(A_5) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_27996])).
% 14.95/6.31  tff(c_32415, plain, (![B_2092]: (v1_relat_1(k2_relat_1(B_2092)) | ~v5_relat_1(B_2092, k1_xboole_0) | ~v1_relat_1(B_2092))), inference(resolution, [status(thm)], [c_32388, c_28001])).
% 14.95/6.31  tff(c_32893, plain, (v1_relat_1('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32877, c_32415])).
% 14.95/6.31  tff(c_32914, plain, (v1_relat_1('#skF_2') | ~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_32893])).
% 14.95/6.31  tff(c_32922, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_32914])).
% 14.95/6.31  tff(c_32926, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_32343, c_32922])).
% 14.95/6.31  tff(c_33468, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33445, c_32926])).
% 14.95/6.31  tff(c_33496, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33445, c_33445, c_12])).
% 14.95/6.31  tff(c_33588, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33496, c_27973])).
% 14.95/6.31  tff(c_33591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33468, c_33588])).
% 14.95/6.31  tff(c_34125, plain, (![C_2253]: (v1_funct_2(C_2253, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2253)!='#skF_2' | ~m1_subset_1(C_2253, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_33401])).
% 14.95/6.31  tff(c_34128, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_32290, c_34125])).
% 14.95/6.31  tff(c_34134, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_33095, c_34128])).
% 14.95/6.31  tff(c_34135, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27961, c_34134])).
% 14.95/6.31  tff(c_34139, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_34135])).
% 14.95/6.31  tff(c_34142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_32877, c_34139])).
% 14.95/6.31  tff(c_34144, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_32914])).
% 14.95/6.31  tff(c_32896, plain, (![A_7]: (r1_tarski('#skF_2', A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32877, c_20])).
% 14.95/6.31  tff(c_34146, plain, (![A_2254]: (r1_tarski('#skF_2', A_2254) | ~v5_relat_1('#skF_3', A_2254))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_32896])).
% 14.95/6.31  tff(c_34161, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_34144, c_34146])).
% 14.95/6.31  tff(c_32812, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_32794])).
% 14.95/6.31  tff(c_34853, plain, (![B_2297, A_2298, C_2299]: (k1_xboole_0=B_2297 | k1_relset_1(A_2298, B_2297, C_2299)=A_2298 | ~v1_funct_2(C_2299, A_2298, B_2297) | ~m1_subset_1(C_2299, k1_zfmisc_1(k2_zfmisc_1(A_2298, B_2297))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_34866, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_34853])).
% 14.95/6.31  tff(c_34878, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_32812, c_34866])).
% 14.95/6.31  tff(c_34880, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_34878])).
% 14.95/6.31  tff(c_34888, plain, (![A_26]: (v1_funct_2('#skF_3', '#skF_1', A_26) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34880, c_54])).
% 14.95/6.31  tff(c_34900, plain, (![A_2300]: (v1_funct_2('#skF_3', '#skF_1', A_2300) | ~r1_tarski('#skF_2', A_2300))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_32877, c_34888])).
% 14.95/6.31  tff(c_34903, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_34900, c_72])).
% 14.95/6.31  tff(c_34906, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34161, c_34903])).
% 14.95/6.31  tff(c_34907, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_34802, c_34906])).
% 14.95/6.31  tff(c_34909, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_34907])).
% 14.95/6.31  tff(c_34885, plain, (![A_26]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_26))) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34880, c_52])).
% 14.95/6.31  tff(c_34967, plain, (![A_2306]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_2306))) | ~r1_tarski('#skF_2', A_2306))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_32877, c_34885])).
% 14.95/6.31  tff(c_34995, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_34967])).
% 14.95/6.31  tff(c_35009, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34161, c_34995])).
% 14.95/6.31  tff(c_35011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34909, c_35009])).
% 14.95/6.31  tff(c_35012, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34907])).
% 14.95/6.31  tff(c_34162, plain, (![B_2083]: (r1_tarski('#skF_2', B_2083) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_32343, c_34146])).
% 14.95/6.31  tff(c_34224, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_34162])).
% 14.95/6.31  tff(c_35030, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35012, c_34224])).
% 14.95/6.31  tff(c_35072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_35030])).
% 14.95/6.31  tff(c_35073, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34878])).
% 14.95/6.31  tff(c_34181, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_34161, c_2])).
% 14.95/6.31  tff(c_34184, plain, (~r1_tarski(k1_xboole_0, '#skF_2')), inference(splitLeft, [status(thm)], [c_34181])).
% 14.95/6.31  tff(c_35092, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35073, c_34184])).
% 14.95/6.31  tff(c_35125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_35092])).
% 14.95/6.31  tff(c_35126, plain, (![B_2083]: (r1_tarski('#skF_2', B_2083))), inference(splitRight, [status(thm)], [c_34162])).
% 14.95/6.31  tff(c_35521, plain, (![B_2330, A_2331, C_2332]: (k1_xboole_0=B_2330 | k1_relset_1(A_2331, B_2330, C_2332)=A_2331 | ~v1_funct_2(C_2332, A_2331, B_2330) | ~m1_subset_1(C_2332, k1_zfmisc_1(k2_zfmisc_1(A_2331, B_2330))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_35534, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_35521])).
% 14.95/6.31  tff(c_35545, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_32812, c_35534])).
% 14.95/6.31  tff(c_35547, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_35545])).
% 14.95/6.31  tff(c_35552, plain, (![A_26]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_26))) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35547, c_52])).
% 14.95/6.31  tff(c_35574, plain, (![A_2334]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_2334))))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_35126, c_32877, c_35552])).
% 14.95/6.31  tff(c_35601, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_35574])).
% 14.95/6.31  tff(c_35555, plain, (![A_26]: (v1_funct_2('#skF_3', '#skF_1', A_26) | ~r1_tarski(k2_relat_1('#skF_3'), A_26) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35547, c_54])).
% 14.95/6.31  tff(c_35564, plain, (![A_2333]: (v1_funct_2('#skF_3', '#skF_1', A_2333))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_35126, c_32877, c_35555])).
% 14.95/6.31  tff(c_35568, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_35564, c_72])).
% 14.95/6.31  tff(c_35800, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35601, c_35568])).
% 14.95/6.31  tff(c_35801, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_35800])).
% 14.95/6.31  tff(c_35835, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35801, c_32356])).
% 14.95/6.31  tff(c_35845, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35801, c_35801, c_10])).
% 14.95/6.31  tff(c_35951, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35845, c_32287])).
% 14.95/6.31  tff(c_35953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35835, c_35951])).
% 14.95/6.31  tff(c_35954, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_35800])).
% 14.95/6.31  tff(c_35127, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_34162])).
% 14.95/6.31  tff(c_35179, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_35127, c_2])).
% 14.95/6.31  tff(c_35337, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_35179])).
% 14.95/6.31  tff(c_35978, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35954, c_35337])).
% 14.95/6.31  tff(c_36019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_35978])).
% 14.95/6.31  tff(c_36020, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_35545])).
% 14.95/6.31  tff(c_36027, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36020, c_35337])).
% 14.95/6.31  tff(c_36064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35126, c_36027])).
% 14.95/6.31  tff(c_36065, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_35179])).
% 14.95/6.31  tff(c_36306, plain, (![B_2363, C_2364, A_2365]: (B_2363='#skF_3' | v1_funct_2(C_2364, A_2365, B_2363) | k1_relset_1(A_2365, B_2363, C_2364)!=A_2365 | ~m1_subset_1(C_2364, k1_zfmisc_1(k2_zfmisc_1(A_2365, B_2363))))), inference(demodulation, [status(thm), theory('equality')], [c_36065, c_46])).
% 14.95/6.31  tff(c_36318, plain, (![C_2364]: ('#skF_3'='#skF_1' | v1_funct_2(C_2364, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2364)!='#skF_2' | ~m1_subset_1(C_2364, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_32287, c_36306])).
% 14.95/6.31  tff(c_36713, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_36318])).
% 14.95/6.31  tff(c_36097, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36065, c_36065, c_12])).
% 14.95/6.31  tff(c_36742, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36713, c_36713, c_36097])).
% 14.95/6.31  tff(c_36765, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36713, c_28048])).
% 14.95/6.31  tff(c_37025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_36742, c_36765])).
% 14.95/6.31  tff(c_38331, plain, (![C_2502]: (v1_funct_2(C_2502, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_2502)!='#skF_2' | ~m1_subset_1(C_2502, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_36318])).
% 14.95/6.31  tff(c_38334, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_32290, c_38331])).
% 14.95/6.31  tff(c_38340, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36341, c_38334])).
% 14.95/6.31  tff(c_38341, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27961, c_38340])).
% 14.95/6.31  tff(c_38345, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_38341])).
% 14.95/6.31  tff(c_38348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_32877, c_38345])).
% 14.95/6.31  tff(c_38349, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34181])).
% 14.95/6.31  tff(c_38370, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38349, c_32356])).
% 14.95/6.31  tff(c_38379, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38349, c_38349, c_12])).
% 14.95/6.31  tff(c_38478, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38379, c_32287])).
% 14.95/6.31  tff(c_38480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38370, c_38478])).
% 14.95/6.31  tff(c_38481, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_32301])).
% 14.95/6.31  tff(c_38546, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_38481])).
% 14.95/6.31  tff(c_40, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_71, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 14.95/6.31  tff(c_38567, plain, (![A_23]: (v1_funct_2('#skF_1', A_23, '#skF_1') | A_23='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38546, c_38546, c_38546, c_38546, c_71])).
% 14.95/6.31  tff(c_38568, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_38567])).
% 14.95/6.31  tff(c_38688, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_16, c_38568])).
% 14.95/6.31  tff(c_38692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_38688])).
% 14.95/6.31  tff(c_38694, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_38567])).
% 14.95/6.31  tff(c_44, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_70, plain, (![C_25, B_24]: (v1_funct_2(C_25, k1_xboole_0, B_24) | k1_relset_1(k1_xboole_0, B_24, C_25)!=k1_xboole_0 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 14.95/6.31  tff(c_39184, plain, (![C_2558, B_2559]: (v1_funct_2(C_2558, '#skF_1', B_2559) | k1_relset_1('#skF_1', B_2559, C_2558)!='#skF_1' | ~m1_subset_1(C_2558, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38546, c_38546, c_38546, c_70])).
% 14.95/6.31  tff(c_39266, plain, (![B_2570]: (v1_funct_2('#skF_1', '#skF_1', B_2570) | k1_relset_1('#skF_1', B_2570, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_38694, c_39184])).
% 14.95/6.31  tff(c_38920, plain, (![A_2528]: (v1_funct_2('#skF_1', A_2528, '#skF_1') | A_2528='#skF_1')), inference(splitRight, [status(thm)], [c_38567])).
% 14.95/6.31  tff(c_38482, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32301])).
% 14.95/6.31  tff(c_38490, plain, (~v1_funct_2(k1_xboole_0, '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38482, c_27961])).
% 14.95/6.31  tff(c_38550, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38490])).
% 14.95/6.31  tff(c_38930, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_38920, c_38550])).
% 14.95/6.31  tff(c_38931, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38930, c_38550])).
% 14.95/6.31  tff(c_39278, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_39266, c_38931])).
% 14.95/6.31  tff(c_38561, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38546, c_12])).
% 14.95/6.31  tff(c_38718, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38561, c_64])).
% 14.95/6.31  tff(c_39002, plain, (![C_2538, B_2539]: (v5_relat_1(C_2538, B_2539) | ~m1_subset_1(C_2538, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_28093])).
% 14.95/6.31  tff(c_39010, plain, (![B_2539]: (v5_relat_1('#skF_3', B_2539))), inference(resolution, [status(thm)], [c_38718, c_39002])).
% 14.95/6.31  tff(c_38552, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38482])).
% 14.95/6.31  tff(c_38742, plain, (![A_2520]: (k1_relat_1(k2_funct_1(A_2520))=k2_relat_1(A_2520) | ~v2_funct_1(A_2520) | ~v1_funct_1(A_2520) | ~v1_relat_1(A_2520))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_38751, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38552, c_38742])).
% 14.95/6.31  tff(c_38755, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_38751])).
% 14.95/6.31  tff(c_38812, plain, (![A_7]: (r1_tarski(k1_relat_1('#skF_1'), A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38755, c_20])).
% 14.95/6.31  tff(c_38822, plain, (![A_7]: (r1_tarski(k1_relat_1('#skF_1'), A_7) | ~v5_relat_1('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_38812])).
% 14.95/6.31  tff(c_39045, plain, (![A_7]: (r1_tarski(k1_relat_1('#skF_1'), A_7))), inference(demodulation, [status(thm), theory('equality')], [c_39010, c_38822])).
% 14.95/6.31  tff(c_28002, plain, (![A_1760]: (v1_relat_1(A_1760) | ~r1_tarski(A_1760, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_27996])).
% 14.95/6.31  tff(c_28007, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_28002])).
% 14.95/6.31  tff(c_38558, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_28007])).
% 14.95/6.31  tff(c_38485, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38482, c_38482, c_32290])).
% 14.95/6.31  tff(c_38536, plain, (![B_4]: (v5_relat_1(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_38485, c_28093])).
% 14.95/6.31  tff(c_38548, plain, (![B_4]: (v5_relat_1('#skF_1', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38536])).
% 14.95/6.31  tff(c_38845, plain, (![A_2523]: (k2_relat_1(k2_funct_1(A_2523))=k1_relat_1(A_2523) | ~v2_funct_1(A_2523) | ~v1_funct_1(A_2523) | ~v1_relat_1(A_2523))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_38863, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38552, c_38845])).
% 14.95/6.31  tff(c_38867, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_38863])).
% 14.95/6.31  tff(c_38871, plain, (![A_7]: (r1_tarski(k1_relat_1('#skF_3'), A_7) | ~v5_relat_1('#skF_1', A_7) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38867, c_20])).
% 14.95/6.31  tff(c_38887, plain, (![A_2524]: (r1_tarski(k1_relat_1('#skF_3'), A_2524))), inference(demodulation, [status(thm), theory('equality')], [c_38558, c_38548, c_38871])).
% 14.95/6.31  tff(c_39081, plain, (![A_2550]: (k1_relat_1('#skF_3')=A_2550 | ~r1_tarski(A_2550, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_38887, c_2])).
% 14.95/6.31  tff(c_39098, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_39045, c_39081])).
% 14.95/6.31  tff(c_39283, plain, (![B_2571, A_2572]: (v1_funct_2(B_2571, k1_relat_1(B_2571), A_2572) | ~r1_tarski(k2_relat_1(B_2571), A_2572) | ~v1_funct_1(B_2571) | ~v1_relat_1(B_2571))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_39289, plain, (![A_2572]: (v1_funct_2('#skF_3', k1_relat_1('#skF_1'), A_2572) | ~r1_tarski(k2_relat_1('#skF_3'), A_2572) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_39098, c_39283])).
% 14.95/6.31  tff(c_39296, plain, (![A_2573]: (v1_funct_2('#skF_3', k1_relat_1('#skF_1'), A_2573))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_39045, c_38755, c_39289])).
% 14.95/6.31  tff(c_38918, plain, (![C_25, A_23]: (C_25='#skF_1' | ~v1_funct_2(C_25, A_23, '#skF_1') | A_23='#skF_1' | ~m1_subset_1(C_25, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38546, c_38546, c_38546, c_72])).
% 14.95/6.31  tff(c_39299, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_1')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_39296, c_38918])).
% 14.95/6.31  tff(c_39302, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38718, c_39299])).
% 14.95/6.31  tff(c_39303, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitLeft, [status(thm)], [c_39302])).
% 14.95/6.31  tff(c_39311, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_39303, c_39045])).
% 14.95/6.31  tff(c_38716, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38561, c_28048])).
% 14.95/6.31  tff(c_39375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39311, c_38716])).
% 14.95/6.31  tff(c_39376, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_39302])).
% 14.95/6.31  tff(c_38934, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38930, c_66])).
% 14.95/6.31  tff(c_39064, plain, (![B_2548, C_2549]: (k1_relset_1('#skF_1', B_2548, C_2549)='#skF_1' | ~v1_funct_2(C_2549, '#skF_1', B_2548) | ~m1_subset_1(C_2549, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38546, c_38546, c_38546, c_38546, c_69])).
% 14.95/6.31  tff(c_39066, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_38934, c_39064])).
% 14.95/6.31  tff(c_39072, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38718, c_39066])).
% 14.95/6.31  tff(c_39381, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39376, c_39072])).
% 14.95/6.31  tff(c_39395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39278, c_39381])).
% 14.95/6.31  tff(c_39396, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_38481])).
% 14.95/6.31  tff(c_39397, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_38481])).
% 14.95/6.31  tff(c_39418, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39396, c_39397])).
% 14.95/6.31  tff(c_39413, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39396, c_39396, c_10])).
% 14.95/6.31  tff(c_39483, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_39413, c_64])).
% 14.95/6.31  tff(c_39629, plain, (![C_2584, A_2585]: (C_2584='#skF_2' | ~v1_funct_2(C_2584, A_2585, '#skF_2') | A_2585='#skF_2' | ~m1_subset_1(C_2584, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_39396, c_39396, c_39396, c_39396, c_72])).
% 14.95/6.31  tff(c_39631, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_39629])).
% 14.95/6.31  tff(c_39634, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39483, c_39631])).
% 14.95/6.31  tff(c_39635, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_39418, c_39634])).
% 14.95/6.31  tff(c_39481, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39413, c_28048])).
% 14.95/6.31  tff(c_39643, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39635, c_39481])).
% 14.95/6.31  tff(c_39660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_39643])).
% 14.95/6.31  tff(c_39661, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_28016])).
% 14.95/6.31  tff(c_39664, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_39661, c_64])).
% 14.95/6.31  tff(c_40072, plain, (![A_2647, B_2648, C_2649]: (k2_relset_1(A_2647, B_2648, C_2649)=k2_relat_1(C_2649) | ~m1_subset_1(C_2649, k1_zfmisc_1(k2_zfmisc_1(A_2647, B_2648))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_40198, plain, (![C_2661]: (k2_relset_1('#skF_1', '#skF_2', C_2661)=k2_relat_1(C_2661) | ~m1_subset_1(C_2661, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_39661, c_40072])).
% 14.95/6.31  tff(c_40201, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_39664, c_40198])).
% 14.95/6.31  tff(c_40207, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_40201])).
% 14.95/6.31  tff(c_40171, plain, (![A_2657, B_2658, C_2659]: (k1_relset_1(A_2657, B_2658, C_2659)=k1_relat_1(C_2659) | ~m1_subset_1(C_2659, k1_zfmisc_1(k2_zfmisc_1(A_2657, B_2658))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_40188, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_27962, c_40171])).
% 14.95/6.31  tff(c_40876, plain, (![B_2729, C_2730, A_2731]: (k1_xboole_0=B_2729 | v1_funct_2(C_2730, A_2731, B_2729) | k1_relset_1(A_2731, B_2729, C_2730)!=A_2731 | ~m1_subset_1(C_2730, k1_zfmisc_1(k2_zfmisc_1(A_2731, B_2729))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 14.95/6.31  tff(c_40885, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_27962, c_40876])).
% 14.95/6.31  tff(c_40898, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40188, c_40885])).
% 14.95/6.31  tff(c_40899, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_27961, c_40898])).
% 14.95/6.31  tff(c_40902, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_40899])).
% 14.95/6.31  tff(c_40905, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_40902])).
% 14.95/6.31  tff(c_40908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_40207, c_40905])).
% 14.95/6.31  tff(c_40909, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_40899])).
% 14.95/6.31  tff(c_39701, plain, (![B_2588, A_2589]: (k1_xboole_0=B_2588 | k1_xboole_0=A_2589 | k2_zfmisc_1(A_2589, B_2588)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.95/6.31  tff(c_39704, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_39661, c_39701])).
% 14.95/6.31  tff(c_39715, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_39704])).
% 14.95/6.31  tff(c_40960, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40909, c_39715])).
% 14.95/6.31  tff(c_40965, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40909, c_40909, c_12])).
% 14.95/6.31  tff(c_41045, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40965, c_39661])).
% 14.95/6.31  tff(c_41047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40960, c_41045])).
% 14.95/6.31  tff(c_41049, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_39704])).
% 14.95/6.31  tff(c_41054, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41049, c_41049, c_12])).
% 14.95/6.31  tff(c_41186, plain, (![C_2750, B_2751, A_2752]: (v5_relat_1(C_2750, B_2751) | ~m1_subset_1(C_2750, k1_zfmisc_1(k2_zfmisc_1(A_2752, B_2751))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.95/6.31  tff(c_41241, plain, (![C_2763, B_2764]: (v5_relat_1(C_2763, B_2764) | ~m1_subset_1(C_2763, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_41054, c_41186])).
% 14.95/6.31  tff(c_41250, plain, (![B_2764]: (v5_relat_1('#skF_3', B_2764))), inference(resolution, [status(thm)], [c_39664, c_41241])).
% 14.95/6.31  tff(c_41055, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41049, c_41049, c_10])).
% 14.95/6.31  tff(c_41438, plain, (![A_2793, B_2794, C_2795]: (k2_relset_1(A_2793, B_2794, C_2795)=k2_relat_1(C_2795) | ~m1_subset_1(C_2795, k1_zfmisc_1(k2_zfmisc_1(A_2793, B_2794))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_41549, plain, (![A_2819, C_2820]: (k2_relset_1(A_2819, '#skF_3', C_2820)=k2_relat_1(C_2820) | ~m1_subset_1(C_2820, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_41055, c_41438])).
% 14.95/6.31  tff(c_41560, plain, (![A_2821]: (k2_relset_1(A_2821, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_39664, c_41549])).
% 14.95/6.31  tff(c_41048, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_39704])).
% 14.95/6.31  tff(c_41075, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41049, c_41049, c_41048])).
% 14.95/6.31  tff(c_41076, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_41075])).
% 14.95/6.31  tff(c_41081, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41076, c_41076, c_60])).
% 14.95/6.31  tff(c_41567, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_41560, c_41081])).
% 14.95/6.31  tff(c_41606, plain, (![A_7]: (r1_tarski('#skF_3', A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_41567, c_20])).
% 14.95/6.31  tff(c_41622, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_41250, c_41606])).
% 14.95/6.31  tff(c_41160, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_41054, c_41076, c_41054, c_41076, c_28015])).
% 14.95/6.31  tff(c_41161, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_41160])).
% 14.95/6.31  tff(c_41627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41622, c_41161])).
% 14.95/6.31  tff(c_41628, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_41160])).
% 14.95/6.31  tff(c_41078, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41076, c_27977])).
% 14.95/6.31  tff(c_41128, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41054, c_41078])).
% 14.95/6.31  tff(c_41136, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_41128, c_2])).
% 14.95/6.31  tff(c_41159, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_41136])).
% 14.95/6.31  tff(c_41668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_41628, c_41159])).
% 14.95/6.31  tff(c_41669, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_41136])).
% 14.95/6.31  tff(c_41844, plain, (![A_2861]: (k2_relat_1(k2_funct_1(A_2861))=k1_relat_1(A_2861) | ~v2_funct_1(A_2861) | ~v1_funct_1(A_2861) | ~v1_relat_1(A_2861))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.95/6.31  tff(c_41865, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_41669, c_41844])).
% 14.95/6.31  tff(c_41869, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_62, c_41865])).
% 14.95/6.31  tff(c_42480, plain, (![A_2917, B_2918, C_2919]: (k2_relset_1(A_2917, B_2918, C_2919)=k2_relat_1(C_2919) | ~m1_subset_1(C_2919, k1_zfmisc_1(k2_zfmisc_1(A_2917, B_2918))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_42598, plain, (![A_2927, C_2928]: (k2_relset_1(A_2927, '#skF_3', C_2928)=k2_relat_1(C_2928) | ~m1_subset_1(C_2928, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_41055, c_42480])).
% 14.95/6.31  tff(c_42600, plain, (![A_2927]: (k2_relset_1(A_2927, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_39664, c_42598])).
% 14.95/6.31  tff(c_42607, plain, (![A_2929]: (k2_relset_1(A_2929, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_41869, c_42600])).
% 14.95/6.31  tff(c_42614, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_42607, c_41081])).
% 14.95/6.31  tff(c_41768, plain, (![C_2843, B_2844, A_2845]: (v5_relat_1(C_2843, B_2844) | ~m1_subset_1(C_2843, k1_zfmisc_1(k2_zfmisc_1(A_2845, B_2844))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.95/6.31  tff(c_41780, plain, (![C_2846, B_2847]: (v5_relat_1(C_2846, B_2847) | ~m1_subset_1(C_2846, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_41054, c_41768])).
% 14.95/6.31  tff(c_41786, plain, (![B_2847]: (v5_relat_1('#skF_3', B_2847))), inference(resolution, [status(thm)], [c_39664, c_41780])).
% 14.95/6.31  tff(c_41883, plain, (![A_7]: (r1_tarski(k1_relat_1('#skF_3'), A_7) | ~v5_relat_1('#skF_3', A_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_41869, c_20])).
% 14.95/6.31  tff(c_41893, plain, (![A_7]: (r1_tarski(k1_relat_1('#skF_3'), A_7))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_41786, c_41883])).
% 14.95/6.31  tff(c_42641, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_42614, c_41893])).
% 14.95/6.31  tff(c_42643, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42614, c_41869])).
% 14.95/6.31  tff(c_42806, plain, (![B_2939, A_2940]: (v1_funct_2(B_2939, k1_relat_1(B_2939), A_2940) | ~r1_tarski(k2_relat_1(B_2939), A_2940) | ~v1_funct_1(B_2939) | ~v1_relat_1(B_2939))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.95/6.31  tff(c_42812, plain, (![A_2940]: (v1_funct_2('#skF_3', '#skF_3', A_2940) | ~r1_tarski(k2_relat_1('#skF_3'), A_2940) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42614, c_42806])).
% 14.95/6.31  tff(c_42818, plain, (![A_2940]: (v1_funct_2('#skF_3', '#skF_3', A_2940))), inference(demodulation, [status(thm), theory('equality')], [c_27995, c_68, c_42641, c_42643, c_42812])).
% 14.95/6.31  tff(c_41080, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41076, c_27961])).
% 14.95/6.31  tff(c_41673, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41669, c_41080])).
% 14.95/6.31  tff(c_42821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42818, c_41673])).
% 14.95/6.31  tff(c_42822, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_41075])).
% 14.95/6.31  tff(c_42823, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_41075])).
% 14.95/6.31  tff(c_42843, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_42823])).
% 14.95/6.31  tff(c_42830, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_27995])).
% 14.95/6.31  tff(c_42838, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_68])).
% 14.95/6.31  tff(c_42837, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_62])).
% 14.95/6.31  tff(c_42829, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_27993])).
% 14.95/6.31  tff(c_42868, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_42822, c_41055])).
% 14.95/6.31  tff(c_42832, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_27962])).
% 14.95/6.31  tff(c_42945, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42868, c_42832])).
% 14.95/6.31  tff(c_42888, plain, (![B_2945]: (k2_zfmisc_1('#skF_1', B_2945)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_42822, c_41054])).
% 14.95/6.31  tff(c_32, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.95/6.31  tff(c_42987, plain, (![C_2954, B_2955]: (v5_relat_1(C_2954, B_2955) | ~m1_subset_1(C_2954, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_42888, c_32])).
% 14.95/6.31  tff(c_42995, plain, (![B_2955]: (v5_relat_1(k2_funct_1('#skF_1'), B_2955))), inference(resolution, [status(thm)], [c_42945, c_42987])).
% 14.95/6.31  tff(c_42827, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_42822, c_39664])).
% 14.95/6.31  tff(c_42996, plain, (![B_2955]: (v5_relat_1('#skF_1', B_2955))), inference(resolution, [status(thm)], [c_42827, c_42987])).
% 14.95/6.31  tff(c_42886, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_42822, c_41054])).
% 14.95/6.31  tff(c_43443, plain, (![A_3013, B_3014, C_3015]: (k2_relset_1(A_3013, B_3014, C_3015)=k2_relat_1(C_3015) | ~m1_subset_1(C_3015, k1_zfmisc_1(k2_zfmisc_1(A_3013, B_3014))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.95/6.31  tff(c_43679, plain, (![B_3043, C_3044]: (k2_relset_1('#skF_1', B_3043, C_3044)=k2_relat_1(C_3044) | ~m1_subset_1(C_3044, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_42886, c_43443])).
% 14.95/6.31  tff(c_43690, plain, (![B_3045]: (k2_relset_1('#skF_1', B_3045, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_42827, c_43679])).
% 14.95/6.31  tff(c_42835, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_60])).
% 14.95/6.31  tff(c_43697, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_43690, c_42835])).
% 14.95/6.31  tff(c_43745, plain, (![A_7]: (r1_tarski('#skF_2', A_7) | ~v5_relat_1('#skF_1', A_7) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_43697, c_20])).
% 14.95/6.31  tff(c_43808, plain, (![A_3049]: (r1_tarski('#skF_2', A_3049))), inference(demodulation, [status(thm), theory('equality')], [c_42830, c_42996, c_43745])).
% 14.95/6.31  tff(c_43947, plain, (![A_3060]: (A_3060='#skF_2' | ~r1_tarski(A_3060, '#skF_2'))), inference(resolution, [status(thm)], [c_43808, c_2])).
% 14.95/6.31  tff(c_44038, plain, (![B_3068]: (k2_relat_1(B_3068)='#skF_2' | ~v5_relat_1(B_3068, '#skF_2') | ~v1_relat_1(B_3068))), inference(resolution, [status(thm)], [c_20, c_43947])).
% 14.95/6.31  tff(c_44126, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_42995, c_44038])).
% 14.95/6.31  tff(c_44190, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42829, c_44126])).
% 14.95/6.31  tff(c_44347, plain, (k1_relat_1('#skF_1')='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44190, c_26])).
% 14.95/6.31  tff(c_44373, plain, (k1_relat_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42830, c_42838, c_42837, c_44347])).
% 14.95/6.31  tff(c_43346, plain, (![A_3003, B_3004, C_3005]: (k1_relset_1(A_3003, B_3004, C_3005)=k1_relat_1(C_3005) | ~m1_subset_1(C_3005, k1_zfmisc_1(k2_zfmisc_1(A_3003, B_3004))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.95/6.31  tff(c_44387, plain, (![A_3069, B_3070, A_3071]: (k1_relset_1(A_3069, B_3070, A_3071)=k1_relat_1(A_3071) | ~r1_tarski(A_3071, k2_zfmisc_1(A_3069, B_3070)))), inference(resolution, [status(thm)], [c_16, c_43346])).
% 14.95/6.31  tff(c_44925, plain, (![B_3102, A_3103]: (k1_relset_1('#skF_1', B_3102, A_3103)=k1_relat_1(A_3103) | ~r1_tarski(A_3103, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42886, c_44387])).
% 14.95/6.31  tff(c_44936, plain, (![B_3102]: (k1_relset_1('#skF_1', B_3102, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_44925])).
% 14.95/6.31  tff(c_44944, plain, (![B_3104]: (k1_relset_1('#skF_1', B_3104, '#skF_1')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44373, c_44936])).
% 14.95/6.31  tff(c_42836, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_66])).
% 14.95/6.31  tff(c_42824, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42822, c_41049])).
% 14.95/6.31  tff(c_43765, plain, (![B_3046, C_3047]: (k1_relset_1('#skF_1', B_3046, C_3047)='#skF_1' | ~v1_funct_2(C_3047, '#skF_1', B_3046) | ~m1_subset_1(C_3047, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42824, c_42824, c_42824, c_42824, c_69])).
% 14.95/6.31  tff(c_43774, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_42836, c_43765])).
% 14.95/6.31  tff(c_43787, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42827, c_43774])).
% 14.95/6.31  tff(c_44948, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_44944, c_43787])).
% 14.95/6.31  tff(c_44955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42843, c_44948])).
% 14.95/6.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.95/6.31  
% 14.95/6.31  Inference rules
% 14.95/6.31  ----------------------
% 14.95/6.31  #Ref     : 0
% 14.95/6.31  #Sup     : 8920
% 14.95/6.31  #Fact    : 0
% 14.95/6.31  #Define  : 0
% 14.95/6.31  #Split   : 117
% 14.95/6.31  #Chain   : 0
% 14.95/6.31  #Close   : 0
% 14.95/6.31  
% 14.95/6.31  Ordering : KBO
% 14.95/6.31  
% 14.95/6.31  Simplification rules
% 14.95/6.31  ----------------------
% 14.95/6.31  #Subsume      : 1199
% 14.95/6.31  #Demod        : 13823
% 14.95/6.31  #Tautology    : 4707
% 14.95/6.31  #SimpNegUnit  : 77
% 14.95/6.31  #BackRed      : 1877
% 14.95/6.31  
% 14.95/6.31  #Partial instantiations: 0
% 14.95/6.31  #Strategies tried      : 1
% 14.95/6.31  
% 14.95/6.31  Timing (in seconds)
% 14.95/6.31  ----------------------
% 14.95/6.31  Preprocessing        : 0.34
% 14.95/6.31  Parsing              : 0.18
% 14.95/6.31  CNF conversion       : 0.02
% 14.95/6.31  Main loop            : 5.00
% 14.95/6.31  Inferencing          : 1.50
% 14.95/6.31  Reduction            : 2.04
% 14.95/6.31  Demodulation         : 1.53
% 14.95/6.31  BG Simplification    : 0.13
% 14.95/6.31  Subsumption          : 0.96
% 14.95/6.31  Abstraction          : 0.18
% 14.95/6.31  MUC search           : 0.00
% 14.95/6.31  Cooper               : 0.00
% 14.95/6.31  Total                : 5.57
% 14.95/6.31  Index Insertion      : 0.00
% 14.95/6.31  Index Deletion       : 0.00
% 14.95/6.31  Index Matching       : 0.00
% 14.95/6.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
