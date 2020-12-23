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
% DateTime   : Thu Dec  3 10:12:35 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :  263 (3987 expanded)
%              Number of leaves         :   38 (1267 expanded)
%              Depth                    :   16
%              Number of atoms          :  486 (10244 expanded)
%              Number of equality atoms :  126 (2214 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_165,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_177,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_165])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3442,plain,(
    ! [A_356,B_357,C_358] :
      ( k2_relset_1(A_356,B_357,C_358) = k2_relat_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3448,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_3442])).

tff(c_3461,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3448])).

tff(c_36,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_21] :
      ( v1_funct_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_138,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_141,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_144,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_141])).

tff(c_146,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_149,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_146])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_149])).

tff(c_162,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_187,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_344,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_358,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_344])).

tff(c_914,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_xboole_0 = B_136
      | k1_relset_1(A_137,B_136,C_138) = A_137
      | ~ v1_funct_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_926,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_914])).

tff(c_944,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_358,c_926])).

tff(c_948,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_944])).

tff(c_34,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_163,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_632,plain,(
    ! [B_112,A_113] :
      ( m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_112),A_113)))
      | ~ r1_tarski(k2_relat_1(B_112),A_113)
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_755,plain,(
    ! [B_122,A_123] :
      ( v1_xboole_0(B_122)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_122),A_123))
      | ~ r1_tarski(k2_relat_1(B_122),A_123)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_632,c_16])).

tff(c_762,plain,(
    ! [B_122] :
      ( v1_xboole_0(B_122)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(B_122),k1_xboole_0)
      | ~ v1_funct_1(B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_755])).

tff(c_770,plain,(
    ! [B_124] :
      ( v1_xboole_0(B_124)
      | ~ r1_tarski(k2_relat_1(B_124),k1_xboole_0)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_762])).

tff(c_1146,plain,(
    ! [A_154] :
      ( v1_xboole_0(k2_funct_1(A_154))
      | ~ r1_tarski(k1_relat_1(A_154),k1_xboole_0)
      | ~ v1_funct_1(k2_funct_1(A_154))
      | ~ v1_relat_1(k2_funct_1(A_154))
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_770])).

tff(c_1149,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_1146])).

tff(c_1157,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_72,c_163,c_1149])).

tff(c_1160,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1157])).

tff(c_1180,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1160])).

tff(c_1184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_1180])).

tff(c_1186,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_384,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_387,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_384])).

tff(c_399,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_387])).

tff(c_418,plain,(
    ! [A_101] :
      ( m1_subset_1(A_101,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_101),k2_relat_1(A_101))))
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1274,plain,(
    ! [A_159] :
      ( m1_subset_1(k2_funct_1(A_159),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_159),k2_relat_1(k2_funct_1(A_159)))))
      | ~ v1_funct_1(k2_funct_1(A_159))
      | ~ v1_relat_1(k2_funct_1(A_159))
      | ~ v2_funct_1(A_159)
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_418])).

tff(c_1303,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_1274])).

tff(c_1327,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_72,c_1186,c_163,c_1303])).

tff(c_1358,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1327])).

tff(c_1377,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_72,c_948,c_1358])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1377])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1410,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_4])).

tff(c_698,plain,(
    ! [B_115] :
      ( m1_subset_1(B_115,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_115),k1_xboole_0)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_632])).

tff(c_701,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_698])).

tff(c_709,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_701])).

tff(c_712,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_1388,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_712])).

tff(c_1516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1388])).

tff(c_1517,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_1537,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1517,c_16])).

tff(c_1556,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1537])).

tff(c_127,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_130,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_127])).

tff(c_1564,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1556,c_130])).

tff(c_1585,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1564,c_1564,c_10])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1587,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1564,c_1564,c_24])).

tff(c_1598,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_399])).

tff(c_188,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_195,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_188])).

tff(c_198,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_1639,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_198])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1556,c_1585,c_1639])).

tff(c_1799,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_1806,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1799,c_130])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1812,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_14])).

tff(c_1817,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_4])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1816,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_26])).

tff(c_1813,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_10])).

tff(c_3000,plain,(
    ! [B_301,A_302] :
      ( m1_subset_1(B_301,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_301),A_302)))
      | ~ r1_tarski(k2_relat_1(B_301),A_302)
      | ~ v1_funct_1(B_301)
      | ~ v1_relat_1(B_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3130,plain,(
    ! [B_317,A_318] :
      ( v1_xboole_0(B_317)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_317),A_318))
      | ~ r1_tarski(k2_relat_1(B_317),A_318)
      | ~ v1_funct_1(B_317)
      | ~ v1_relat_1(B_317) ) ),
    inference(resolution,[status(thm)],[c_3000,c_16])).

tff(c_3137,plain,(
    ! [B_317] :
      ( v1_xboole_0(B_317)
      | ~ v1_xboole_0('#skF_3')
      | ~ r1_tarski(k2_relat_1(B_317),'#skF_3')
      | ~ v1_funct_1(B_317)
      | ~ v1_relat_1(B_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1813,c_3130])).

tff(c_3145,plain,(
    ! [B_319] :
      ( v1_xboole_0(B_319)
      | ~ r1_tarski(k2_relat_1(B_319),'#skF_3')
      | ~ v1_funct_1(B_319)
      | ~ v1_relat_1(B_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_3137])).

tff(c_3237,plain,(
    ! [A_331] :
      ( v1_xboole_0(k2_funct_1(A_331))
      | ~ r1_tarski(k1_relat_1(A_331),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(A_331))
      | ~ v1_relat_1(k2_funct_1(A_331))
      | ~ v2_funct_1(A_331)
      | ~ v1_funct_1(A_331)
      | ~ v1_relat_1(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3145])).

tff(c_3243,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1816,c_3237])).

tff(c_3245,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_72,c_163,c_1817,c_3243])).

tff(c_3258,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3245])).

tff(c_3261,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3258])).

tff(c_3265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_3261])).

tff(c_3266,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3245])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1807,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_1799,c_6])).

tff(c_3285,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3266,c_1807])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1814,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_12])).

tff(c_1800,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_1856,plain,(
    ! [A_175] :
      ( A_175 = '#skF_3'
      | ~ v1_xboole_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_1799,c_6])).

tff(c_1863,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1800,c_1856])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1923,plain,(
    ! [B_179,A_180] :
      ( B_179 = '#skF_3'
      | A_180 = '#skF_3'
      | k2_zfmisc_1(A_180,B_179) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_1806,c_8])).

tff(c_1933,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1863,c_1923])).

tff(c_1938,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1933])).

tff(c_1942,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1812])).

tff(c_1952,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_177])).

tff(c_1957,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_78])).

tff(c_1956,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_72])).

tff(c_1953,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_163])).

tff(c_1947,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1938,c_1816])).

tff(c_2107,plain,(
    ! [A_199] :
      ( k2_relat_1(k2_funct_1(A_199)) = k1_relat_1(A_199)
      | ~ v2_funct_1(A_199)
      | ~ v1_funct_1(A_199)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [A_35] :
      ( v1_funct_2(A_35,k1_relat_1(A_35),k2_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2599,plain,(
    ! [A_258] :
      ( v1_funct_2(k2_funct_1(A_258),k1_relat_1(k2_funct_1(A_258)),k1_relat_1(A_258))
      | ~ v1_funct_1(k2_funct_1(A_258))
      | ~ v1_relat_1(k2_funct_1(A_258))
      | ~ v2_funct_1(A_258)
      | ~ v1_funct_1(A_258)
      | ~ v1_relat_1(A_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2107,c_58])).

tff(c_2608,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1947,c_2599])).

tff(c_2610,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1957,c_1956,c_1953,c_2608])).

tff(c_2611,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2610])).

tff(c_2614,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2611])).

tff(c_2618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1957,c_2614])).

tff(c_2620,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2610])).

tff(c_1946,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1817])).

tff(c_1950,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1799])).

tff(c_1945,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1938,c_1813])).

tff(c_2404,plain,(
    ! [B_233,A_234] :
      ( m1_subset_1(B_233,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_233),A_234)))
      | ~ r1_tarski(k2_relat_1(B_233),A_234)
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2512,plain,(
    ! [B_243,A_244] :
      ( v1_xboole_0(B_243)
      | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_243),A_244))
      | ~ r1_tarski(k2_relat_1(B_243),A_244)
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_2404,c_16])).

tff(c_2519,plain,(
    ! [B_243] :
      ( v1_xboole_0(B_243)
      | ~ v1_xboole_0('#skF_1')
      | ~ r1_tarski(k2_relat_1(B_243),'#skF_1')
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1945,c_2512])).

tff(c_2569,plain,(
    ! [B_250] :
      ( v1_xboole_0(B_250)
      | ~ r1_tarski(k2_relat_1(B_250),'#skF_1')
      | ~ v1_funct_1(B_250)
      | ~ v1_relat_1(B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1950,c_2519])).

tff(c_2645,plain,(
    ! [A_260] :
      ( v1_xboole_0(k2_funct_1(A_260))
      | ~ r1_tarski(k1_relat_1(A_260),'#skF_1')
      | ~ v1_funct_1(k2_funct_1(A_260))
      | ~ v1_relat_1(k2_funct_1(A_260))
      | ~ v2_funct_1(A_260)
      | ~ v1_funct_1(A_260)
      | ~ v1_relat_1(A_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2569])).

tff(c_2651,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1947,c_2645])).

tff(c_2653,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1957,c_1956,c_2620,c_1953,c_1946,c_2651])).

tff(c_1944,plain,(
    ! [A_2] :
      ( A_2 = '#skF_1'
      | ~ v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1807])).

tff(c_2659,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2653,c_1944])).

tff(c_1951,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_187])).

tff(c_2060,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_1951])).

tff(c_2665,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_2060])).

tff(c_2673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1942,c_2665])).

tff(c_2674,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1933])).

tff(c_2688,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2674,c_187])).

tff(c_2692,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1814,c_2688])).

tff(c_3289,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3285,c_2692])).

tff(c_3295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1812,c_3289])).

tff(c_3296,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_3297,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_3545,plain,(
    ! [A_366,B_367,C_368] :
      ( k1_relset_1(A_366,B_367,C_368) = k1_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3566,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3297,c_3545])).

tff(c_3860,plain,(
    ! [B_391,C_392,A_393] :
      ( k1_xboole_0 = B_391
      | v1_funct_2(C_392,A_393,B_391)
      | k1_relset_1(A_393,B_391,C_392) != A_393
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_393,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_3872,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3297,c_3860])).

tff(c_3892,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_3872])).

tff(c_3893,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3296,c_3892])).

tff(c_3899,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3893])).

tff(c_3902,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3899])).

tff(c_3905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_72,c_3461,c_3902])).

tff(c_3906,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3893])).

tff(c_3934,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_2])).

tff(c_3929,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_3906,c_10])).

tff(c_3302,plain,(
    ! [B_334,A_335] :
      ( v1_xboole_0(B_334)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(A_335))
      | ~ v1_xboole_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3312,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3297,c_3302])).

tff(c_3317,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3312])).

tff(c_4188,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3929,c_3317])).

tff(c_4192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3934,c_4188])).

tff(c_4194,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3312])).

tff(c_4207,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4194,c_130])).

tff(c_4243,plain,(
    ! [B_401,A_402] :
      ( k1_xboole_0 = B_401
      | k1_xboole_0 = A_402
      | k2_zfmisc_1(A_402,B_401) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4253,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4207,c_4243])).

tff(c_4258,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4253])).

tff(c_4274,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4258,c_2])).

tff(c_4269,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4258,c_4258,c_10])).

tff(c_3313,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_3302])).

tff(c_3316,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3313])).

tff(c_4312,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4269,c_3316])).

tff(c_4316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4274,c_4312])).

tff(c_4317,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4253])).

tff(c_4334,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4317,c_2])).

tff(c_4330,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4317,c_4317,c_12])).

tff(c_4409,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4330,c_3316])).

tff(c_4413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4334,c_4409])).

tff(c_4414,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3313])).

tff(c_4421,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4414,c_130])).

tff(c_4444,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4])).

tff(c_4442,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_24])).

tff(c_4443,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_26])).

tff(c_4957,plain,(
    ! [B_461,A_462] :
      ( v1_funct_2(B_461,k1_relat_1(B_461),A_462)
      | ~ r1_tarski(k2_relat_1(B_461),A_462)
      | ~ v1_funct_1(B_461)
      | ~ v1_relat_1(B_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4966,plain,(
    ! [A_462] :
      ( v1_funct_2('#skF_3','#skF_3',A_462)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_462)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4443,c_4957])).

tff(c_4969,plain,(
    ! [A_462] : v1_funct_2('#skF_3','#skF_3',A_462) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_4444,c_4442,c_4966])).

tff(c_4441,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_12])).

tff(c_4415,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3313])).

tff(c_4509,plain,(
    ! [A_418] :
      ( A_418 = '#skF_3'
      | ~ v1_xboole_0(A_418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_130])).

tff(c_4516,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4415,c_4509])).

tff(c_4576,plain,(
    ! [B_426,A_427] :
      ( B_426 = '#skF_3'
      | A_427 = '#skF_3'
      | k2_zfmisc_1(A_427,B_426) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_4421,c_8])).

tff(c_4586,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4516,c_4576])).

tff(c_4591,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4586])).

tff(c_4605,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_4414])).

tff(c_4440,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_10])).

tff(c_4598,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_4591,c_4440])).

tff(c_4551,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3312])).

tff(c_4683,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4598,c_4551])).

tff(c_4686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4605,c_4683])).

tff(c_4687,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4586])).

tff(c_4689,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4687,c_4551])).

tff(c_4697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4414,c_4441,c_4689])).

tff(c_4699,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3312])).

tff(c_4436,plain,(
    ! [A_46] :
      ( A_46 = '#skF_3'
      | ~ v1_xboole_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_130])).

tff(c_4735,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4699,c_4436])).

tff(c_4762,plain,(
    ! [B_435,A_436] :
      ( B_435 = '#skF_3'
      | A_436 = '#skF_3'
      | k2_zfmisc_1(A_436,B_435) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_4421,c_8])).

tff(c_4775,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4735,c_4762])).

tff(c_4781,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4775])).

tff(c_4698,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3312])).

tff(c_4705,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4698,c_4436])).

tff(c_4710,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4705,c_3296])).

tff(c_4783,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4781,c_4710])).

tff(c_4973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4969,c_4783])).

tff(c_4974,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4775])).

tff(c_4975,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4775])).

tff(c_5002,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4974,c_4975])).

tff(c_44,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_80,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_4437,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_3',A_32,'#skF_3')
      | A_32 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4421,c_4421,c_4421,c_80])).

tff(c_5160,plain,(
    ! [A_475] :
      ( v1_funct_2('#skF_1',A_475,'#skF_1')
      | A_475 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4974,c_4974,c_4974,c_4437])).

tff(c_4979,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4974,c_4710])).

tff(c_5163,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5160,c_4979])).

tff(c_5167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5002,c_5163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:39:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.17  
% 5.92/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.17  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.92/2.17  
% 5.92/2.17  %Foreground sorts:
% 5.92/2.17  
% 5.92/2.17  
% 5.92/2.17  %Background operators:
% 5.92/2.17  
% 5.92/2.17  
% 5.92/2.17  %Foreground operators:
% 5.92/2.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.92/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.92/2.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.92/2.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.92/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.92/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.92/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.92/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.92/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.92/2.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.92/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.92/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.92/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.92/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.92/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.17  
% 6.14/2.21  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.14/2.21  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.14/2.21  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.14/2.21  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.14/2.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.14/2.21  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.14/2.21  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.14/2.21  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.14/2.21  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.14/2.21  tff(f_148, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.14/2.21  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.14/2.21  tff(f_136, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.14/2.21  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.14/2.21  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.14/2.21  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.14/2.21  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.14/2.21  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.14/2.21  tff(c_165, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.14/2.21  tff(c_177, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_165])).
% 6.14/2.21  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.14/2.21  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.14/2.21  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.14/2.21  tff(c_3442, plain, (![A_356, B_357, C_358]: (k2_relset_1(A_356, B_357, C_358)=k2_relat_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.14/2.21  tff(c_3448, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_3442])).
% 6.14/2.21  tff(c_3461, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3448])).
% 6.14/2.21  tff(c_36, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.14/2.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.14/2.21  tff(c_30, plain, (![A_21]: (v1_funct_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.14/2.21  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.14/2.21  tff(c_138, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_68])).
% 6.14/2.21  tff(c_141, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_138])).
% 6.14/2.21  tff(c_144, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_141])).
% 6.14/2.21  tff(c_146, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.14/2.21  tff(c_149, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_146])).
% 6.14/2.21  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144, c_149])).
% 6.14/2.21  tff(c_162, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_68])).
% 6.14/2.21  tff(c_187, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_162])).
% 6.14/2.21  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.14/2.21  tff(c_344, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.14/2.21  tff(c_358, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_344])).
% 6.14/2.21  tff(c_914, plain, (![B_136, A_137, C_138]: (k1_xboole_0=B_136 | k1_relset_1(A_137, B_136, C_138)=A_137 | ~v1_funct_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.14/2.21  tff(c_926, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_914])).
% 6.14/2.21  tff(c_944, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_358, c_926])).
% 6.14/2.21  tff(c_948, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_944])).
% 6.14/2.21  tff(c_34, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.14/2.21  tff(c_32, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.14/2.21  tff(c_163, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_68])).
% 6.14/2.21  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.14/2.21  tff(c_632, plain, (![B_112, A_113]: (m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_112), A_113))) | ~r1_tarski(k2_relat_1(B_112), A_113) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.14/2.21  tff(c_16, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.14/2.21  tff(c_755, plain, (![B_122, A_123]: (v1_xboole_0(B_122) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_122), A_123)) | ~r1_tarski(k2_relat_1(B_122), A_123) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_632, c_16])).
% 6.14/2.21  tff(c_762, plain, (![B_122]: (v1_xboole_0(B_122) | ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k2_relat_1(B_122), k1_xboole_0) | ~v1_funct_1(B_122) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_10, c_755])).
% 6.14/2.21  tff(c_770, plain, (![B_124]: (v1_xboole_0(B_124) | ~r1_tarski(k2_relat_1(B_124), k1_xboole_0) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_762])).
% 6.14/2.21  tff(c_1146, plain, (![A_154]: (v1_xboole_0(k2_funct_1(A_154)) | ~r1_tarski(k1_relat_1(A_154), k1_xboole_0) | ~v1_funct_1(k2_funct_1(A_154)) | ~v1_relat_1(k2_funct_1(A_154)) | ~v2_funct_1(A_154) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(superposition, [status(thm), theory('equality')], [c_34, c_770])).
% 6.14/2.21  tff(c_1149, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_948, c_1146])).
% 6.14/2.21  tff(c_1157, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_72, c_163, c_1149])).
% 6.14/2.21  tff(c_1160, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1157])).
% 6.14/2.21  tff(c_1180, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1160])).
% 6.14/2.21  tff(c_1184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_1180])).
% 6.14/2.21  tff(c_1186, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1157])).
% 6.14/2.21  tff(c_384, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.14/2.21  tff(c_387, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_384])).
% 6.14/2.21  tff(c_399, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_387])).
% 6.14/2.21  tff(c_418, plain, (![A_101]: (m1_subset_1(A_101, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_101), k2_relat_1(A_101)))) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.14/2.21  tff(c_1274, plain, (![A_159]: (m1_subset_1(k2_funct_1(A_159), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_159), k2_relat_1(k2_funct_1(A_159))))) | ~v1_funct_1(k2_funct_1(A_159)) | ~v1_relat_1(k2_funct_1(A_159)) | ~v2_funct_1(A_159) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_36, c_418])).
% 6.14/2.21  tff(c_1303, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_399, c_1274])).
% 6.14/2.21  tff(c_1327, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_72, c_1186, c_163, c_1303])).
% 6.14/2.21  tff(c_1358, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1327])).
% 6.14/2.21  tff(c_1377, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_72, c_948, c_1358])).
% 6.14/2.21  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_1377])).
% 6.14/2.21  tff(c_1380, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_944])).
% 6.14/2.21  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 6.14/2.21  tff(c_1410, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_4])).
% 6.14/2.21  tff(c_698, plain, (![B_115]: (m1_subset_1(B_115, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_115), k1_xboole_0) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115))), inference(superposition, [status(thm), theory('equality')], [c_10, c_632])).
% 6.14/2.21  tff(c_701, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_399, c_698])).
% 6.14/2.21  tff(c_709, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_701])).
% 6.14/2.21  tff(c_712, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_709])).
% 6.14/2.21  tff(c_1388, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_712])).
% 6.14/2.21  tff(c_1516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1388])).
% 6.14/2.21  tff(c_1517, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_709])).
% 6.14/2.21  tff(c_1537, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1517, c_16])).
% 6.14/2.21  tff(c_1556, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1537])).
% 6.14/2.21  tff(c_127, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.14/2.21  tff(c_130, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_127])).
% 6.14/2.21  tff(c_1564, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1556, c_130])).
% 6.14/2.21  tff(c_1585, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1564, c_1564, c_10])).
% 6.14/2.21  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.14/2.21  tff(c_1587, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1564, c_1564, c_24])).
% 6.14/2.21  tff(c_1598, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_399])).
% 6.14/2.21  tff(c_188, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.14/2.21  tff(c_195, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_188])).
% 6.14/2.21  tff(c_198, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_195])).
% 6.14/2.21  tff(c_1639, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1598, c_198])).
% 6.14/2.21  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1556, c_1585, c_1639])).
% 6.14/2.21  tff(c_1799, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_195])).
% 6.14/2.21  tff(c_1806, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1799, c_130])).
% 6.14/2.21  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.14/2.21  tff(c_1812, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_14])).
% 6.14/2.21  tff(c_1817, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_4])).
% 6.14/2.21  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.14/2.21  tff(c_1816, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_26])).
% 6.14/2.21  tff(c_1813, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_10])).
% 6.14/2.21  tff(c_3000, plain, (![B_301, A_302]: (m1_subset_1(B_301, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_301), A_302))) | ~r1_tarski(k2_relat_1(B_301), A_302) | ~v1_funct_1(B_301) | ~v1_relat_1(B_301))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.14/2.21  tff(c_3130, plain, (![B_317, A_318]: (v1_xboole_0(B_317) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_317), A_318)) | ~r1_tarski(k2_relat_1(B_317), A_318) | ~v1_funct_1(B_317) | ~v1_relat_1(B_317))), inference(resolution, [status(thm)], [c_3000, c_16])).
% 6.14/2.21  tff(c_3137, plain, (![B_317]: (v1_xboole_0(B_317) | ~v1_xboole_0('#skF_3') | ~r1_tarski(k2_relat_1(B_317), '#skF_3') | ~v1_funct_1(B_317) | ~v1_relat_1(B_317))), inference(superposition, [status(thm), theory('equality')], [c_1813, c_3130])).
% 6.14/2.21  tff(c_3145, plain, (![B_319]: (v1_xboole_0(B_319) | ~r1_tarski(k2_relat_1(B_319), '#skF_3') | ~v1_funct_1(B_319) | ~v1_relat_1(B_319))), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_3137])).
% 6.14/2.21  tff(c_3237, plain, (![A_331]: (v1_xboole_0(k2_funct_1(A_331)) | ~r1_tarski(k1_relat_1(A_331), '#skF_3') | ~v1_funct_1(k2_funct_1(A_331)) | ~v1_relat_1(k2_funct_1(A_331)) | ~v2_funct_1(A_331) | ~v1_funct_1(A_331) | ~v1_relat_1(A_331))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3145])).
% 6.14/2.21  tff(c_3243, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1816, c_3237])).
% 6.14/2.21  tff(c_3245, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_72, c_163, c_1817, c_3243])).
% 6.14/2.21  tff(c_3258, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3245])).
% 6.14/2.21  tff(c_3261, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3258])).
% 6.14/2.21  tff(c_3265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_3261])).
% 6.14/2.21  tff(c_3266, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3245])).
% 6.14/2.21  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.14/2.21  tff(c_1807, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_1799, c_6])).
% 6.14/2.21  tff(c_3285, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3266, c_1807])).
% 6.14/2.21  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.14/2.21  tff(c_1814, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_12])).
% 6.14/2.21  tff(c_1800, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_195])).
% 6.14/2.21  tff(c_1856, plain, (![A_175]: (A_175='#skF_3' | ~v1_xboole_0(A_175))), inference(resolution, [status(thm)], [c_1799, c_6])).
% 6.14/2.21  tff(c_1863, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1800, c_1856])).
% 6.14/2.21  tff(c_8, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.14/2.21  tff(c_1923, plain, (![B_179, A_180]: (B_179='#skF_3' | A_180='#skF_3' | k2_zfmisc_1(A_180, B_179)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_1806, c_8])).
% 6.14/2.21  tff(c_1933, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1863, c_1923])).
% 6.14/2.21  tff(c_1938, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_1933])).
% 6.14/2.21  tff(c_1942, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1812])).
% 6.14/2.21  tff(c_1952, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_177])).
% 6.14/2.21  tff(c_1957, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_78])).
% 6.14/2.21  tff(c_1956, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_72])).
% 6.14/2.21  tff(c_1953, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_163])).
% 6.14/2.21  tff(c_1947, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1938, c_1816])).
% 6.14/2.21  tff(c_2107, plain, (![A_199]: (k2_relat_1(k2_funct_1(A_199))=k1_relat_1(A_199) | ~v2_funct_1(A_199) | ~v1_funct_1(A_199) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.14/2.21  tff(c_58, plain, (![A_35]: (v1_funct_2(A_35, k1_relat_1(A_35), k2_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.14/2.21  tff(c_2599, plain, (![A_258]: (v1_funct_2(k2_funct_1(A_258), k1_relat_1(k2_funct_1(A_258)), k1_relat_1(A_258)) | ~v1_funct_1(k2_funct_1(A_258)) | ~v1_relat_1(k2_funct_1(A_258)) | ~v2_funct_1(A_258) | ~v1_funct_1(A_258) | ~v1_relat_1(A_258))), inference(superposition, [status(thm), theory('equality')], [c_2107, c_58])).
% 6.14/2.21  tff(c_2608, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1947, c_2599])).
% 6.14/2.21  tff(c_2610, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1957, c_1956, c_1953, c_2608])).
% 6.14/2.21  tff(c_2611, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2610])).
% 6.14/2.21  tff(c_2614, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2611])).
% 6.14/2.21  tff(c_2618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1957, c_2614])).
% 6.14/2.21  tff(c_2620, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_2610])).
% 6.14/2.21  tff(c_1946, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1817])).
% 6.14/2.21  tff(c_1950, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1799])).
% 6.14/2.21  tff(c_1945, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1938, c_1813])).
% 6.14/2.21  tff(c_2404, plain, (![B_233, A_234]: (m1_subset_1(B_233, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_233), A_234))) | ~r1_tarski(k2_relat_1(B_233), A_234) | ~v1_funct_1(B_233) | ~v1_relat_1(B_233))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.14/2.21  tff(c_2512, plain, (![B_243, A_244]: (v1_xboole_0(B_243) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(B_243), A_244)) | ~r1_tarski(k2_relat_1(B_243), A_244) | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(resolution, [status(thm)], [c_2404, c_16])).
% 6.14/2.21  tff(c_2519, plain, (![B_243]: (v1_xboole_0(B_243) | ~v1_xboole_0('#skF_1') | ~r1_tarski(k2_relat_1(B_243), '#skF_1') | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(superposition, [status(thm), theory('equality')], [c_1945, c_2512])).
% 6.14/2.21  tff(c_2569, plain, (![B_250]: (v1_xboole_0(B_250) | ~r1_tarski(k2_relat_1(B_250), '#skF_1') | ~v1_funct_1(B_250) | ~v1_relat_1(B_250))), inference(demodulation, [status(thm), theory('equality')], [c_1950, c_2519])).
% 6.14/2.21  tff(c_2645, plain, (![A_260]: (v1_xboole_0(k2_funct_1(A_260)) | ~r1_tarski(k1_relat_1(A_260), '#skF_1') | ~v1_funct_1(k2_funct_1(A_260)) | ~v1_relat_1(k2_funct_1(A_260)) | ~v2_funct_1(A_260) | ~v1_funct_1(A_260) | ~v1_relat_1(A_260))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2569])).
% 6.14/2.21  tff(c_2651, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~r1_tarski('#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1947, c_2645])).
% 6.14/2.21  tff(c_2653, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1957, c_1956, c_2620, c_1953, c_1946, c_2651])).
% 6.14/2.21  tff(c_1944, plain, (![A_2]: (A_2='#skF_1' | ~v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1807])).
% 6.14/2.21  tff(c_2659, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_2653, c_1944])).
% 6.14/2.21  tff(c_1951, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_187])).
% 6.14/2.21  tff(c_2060, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_1951])).
% 6.14/2.21  tff(c_2665, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2659, c_2060])).
% 6.14/2.21  tff(c_2673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1942, c_2665])).
% 6.14/2.21  tff(c_2674, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1933])).
% 6.14/2.21  tff(c_2688, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2674, c_187])).
% 6.14/2.21  tff(c_2692, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1814, c_2688])).
% 6.14/2.21  tff(c_3289, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3285, c_2692])).
% 6.14/2.21  tff(c_3295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1812, c_3289])).
% 6.14/2.21  tff(c_3296, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_162])).
% 6.14/2.21  tff(c_3297, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_162])).
% 6.14/2.21  tff(c_3545, plain, (![A_366, B_367, C_368]: (k1_relset_1(A_366, B_367, C_368)=k1_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.14/2.21  tff(c_3566, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3297, c_3545])).
% 6.14/2.21  tff(c_3860, plain, (![B_391, C_392, A_393]: (k1_xboole_0=B_391 | v1_funct_2(C_392, A_393, B_391) | k1_relset_1(A_393, B_391, C_392)!=A_393 | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_393, B_391))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.14/2.21  tff(c_3872, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3297, c_3860])).
% 6.14/2.21  tff(c_3892, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_3872])).
% 6.14/2.21  tff(c_3893, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3296, c_3892])).
% 6.14/2.21  tff(c_3899, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3893])).
% 6.14/2.21  tff(c_3902, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_3899])).
% 6.14/2.21  tff(c_3905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_72, c_3461, c_3902])).
% 6.14/2.21  tff(c_3906, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3893])).
% 6.14/2.21  tff(c_3934, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_2])).
% 6.14/2.21  tff(c_3929, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3906, c_3906, c_10])).
% 6.14/2.21  tff(c_3302, plain, (![B_334, A_335]: (v1_xboole_0(B_334) | ~m1_subset_1(B_334, k1_zfmisc_1(A_335)) | ~v1_xboole_0(A_335))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.14/2.21  tff(c_3312, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_3297, c_3302])).
% 6.14/2.21  tff(c_3317, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3312])).
% 6.14/2.21  tff(c_4188, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3929, c_3317])).
% 6.14/2.21  tff(c_4192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3934, c_4188])).
% 6.14/2.21  tff(c_4194, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_3312])).
% 6.14/2.21  tff(c_4207, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_4194, c_130])).
% 6.14/2.21  tff(c_4243, plain, (![B_401, A_402]: (k1_xboole_0=B_401 | k1_xboole_0=A_402 | k2_zfmisc_1(A_402, B_401)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.14/2.21  tff(c_4253, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4207, c_4243])).
% 6.14/2.21  tff(c_4258, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4253])).
% 6.14/2.21  tff(c_4274, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4258, c_2])).
% 6.14/2.21  tff(c_4269, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4258, c_4258, c_10])).
% 6.14/2.21  tff(c_3313, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_3302])).
% 6.14/2.21  tff(c_3316, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3313])).
% 6.14/2.21  tff(c_4312, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4269, c_3316])).
% 6.14/2.21  tff(c_4316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4274, c_4312])).
% 6.14/2.21  tff(c_4317, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4253])).
% 6.14/2.21  tff(c_4334, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4317, c_2])).
% 6.14/2.21  tff(c_4330, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4317, c_4317, c_12])).
% 6.14/2.21  tff(c_4409, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4330, c_3316])).
% 6.14/2.21  tff(c_4413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4334, c_4409])).
% 6.14/2.21  tff(c_4414, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3313])).
% 6.14/2.21  tff(c_4421, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4414, c_130])).
% 6.14/2.21  tff(c_4444, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4])).
% 6.14/2.21  tff(c_4442, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_24])).
% 6.14/2.21  tff(c_4443, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_26])).
% 6.14/2.21  tff(c_4957, plain, (![B_461, A_462]: (v1_funct_2(B_461, k1_relat_1(B_461), A_462) | ~r1_tarski(k2_relat_1(B_461), A_462) | ~v1_funct_1(B_461) | ~v1_relat_1(B_461))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.14/2.21  tff(c_4966, plain, (![A_462]: (v1_funct_2('#skF_3', '#skF_3', A_462) | ~r1_tarski(k2_relat_1('#skF_3'), A_462) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4443, c_4957])).
% 6.14/2.21  tff(c_4969, plain, (![A_462]: (v1_funct_2('#skF_3', '#skF_3', A_462))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_4444, c_4442, c_4966])).
% 6.14/2.21  tff(c_4441, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_12])).
% 6.14/2.21  tff(c_4415, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3313])).
% 6.14/2.21  tff(c_4509, plain, (![A_418]: (A_418='#skF_3' | ~v1_xboole_0(A_418))), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_130])).
% 6.14/2.21  tff(c_4516, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_4415, c_4509])).
% 6.14/2.21  tff(c_4576, plain, (![B_426, A_427]: (B_426='#skF_3' | A_427='#skF_3' | k2_zfmisc_1(A_427, B_426)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_4421, c_8])).
% 6.14/2.21  tff(c_4586, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4516, c_4576])).
% 6.14/2.21  tff(c_4591, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_4586])).
% 6.14/2.21  tff(c_4605, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4591, c_4414])).
% 6.14/2.21  tff(c_4440, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_10])).
% 6.14/2.21  tff(c_4598, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4591, c_4591, c_4440])).
% 6.14/2.21  tff(c_4551, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3312])).
% 6.14/2.21  tff(c_4683, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4598, c_4551])).
% 6.14/2.21  tff(c_4686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4605, c_4683])).
% 6.14/2.21  tff(c_4687, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4586])).
% 6.14/2.21  tff(c_4689, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4687, c_4551])).
% 6.14/2.21  tff(c_4697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4414, c_4441, c_4689])).
% 6.14/2.21  tff(c_4699, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_3312])).
% 6.14/2.21  tff(c_4436, plain, (![A_46]: (A_46='#skF_3' | ~v1_xboole_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_130])).
% 6.14/2.21  tff(c_4735, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_4699, c_4436])).
% 6.14/2.21  tff(c_4762, plain, (![B_435, A_436]: (B_435='#skF_3' | A_436='#skF_3' | k2_zfmisc_1(A_436, B_435)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_4421, c_8])).
% 6.14/2.21  tff(c_4775, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4735, c_4762])).
% 6.14/2.21  tff(c_4781, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_4775])).
% 6.14/2.21  tff(c_4698, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3312])).
% 6.14/2.21  tff(c_4705, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4698, c_4436])).
% 6.14/2.21  tff(c_4710, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4705, c_3296])).
% 6.14/2.21  tff(c_4783, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4781, c_4710])).
% 6.14/2.21  tff(c_4973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4969, c_4783])).
% 6.14/2.21  tff(c_4974, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_4775])).
% 6.14/2.21  tff(c_4975, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_4775])).
% 6.14/2.21  tff(c_5002, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4974, c_4975])).
% 6.14/2.21  tff(c_44, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.14/2.21  tff(c_80, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 6.14/2.21  tff(c_4437, plain, (![A_32]: (v1_funct_2('#skF_3', A_32, '#skF_3') | A_32='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4421, c_4421, c_4421, c_80])).
% 6.14/2.21  tff(c_5160, plain, (![A_475]: (v1_funct_2('#skF_1', A_475, '#skF_1') | A_475='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4974, c_4974, c_4974, c_4437])).
% 6.14/2.21  tff(c_4979, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4974, c_4710])).
% 6.14/2.21  tff(c_5163, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_5160, c_4979])).
% 6.14/2.21  tff(c_5167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5002, c_5163])).
% 6.14/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.14/2.21  
% 6.14/2.21  Inference rules
% 6.14/2.21  ----------------------
% 6.14/2.21  #Ref     : 0
% 6.14/2.21  #Sup     : 1075
% 6.14/2.21  #Fact    : 0
% 6.14/2.21  #Define  : 0
% 6.14/2.21  #Split   : 25
% 6.14/2.21  #Chain   : 0
% 6.14/2.21  #Close   : 0
% 6.14/2.21  
% 6.14/2.21  Ordering : KBO
% 6.14/2.21  
% 6.14/2.21  Simplification rules
% 6.14/2.21  ----------------------
% 6.14/2.21  #Subsume      : 103
% 6.14/2.21  #Demod        : 1689
% 6.14/2.21  #Tautology    : 643
% 6.14/2.21  #SimpNegUnit  : 8
% 6.14/2.21  #BackRed      : 285
% 6.14/2.21  
% 6.14/2.21  #Partial instantiations: 0
% 6.14/2.21  #Strategies tried      : 1
% 6.14/2.21  
% 6.14/2.21  Timing (in seconds)
% 6.14/2.21  ----------------------
% 6.14/2.21  Preprocessing        : 0.37
% 6.14/2.21  Parsing              : 0.20
% 6.14/2.21  CNF conversion       : 0.02
% 6.14/2.21  Main loop            : 1.02
% 6.14/2.21  Inferencing          : 0.35
% 6.14/2.21  Reduction            : 0.37
% 6.14/2.21  Demodulation         : 0.27
% 6.14/2.21  BG Simplification    : 0.04
% 6.14/2.21  Subsumption          : 0.17
% 6.14/2.21  Abstraction          : 0.04
% 6.14/2.21  MUC search           : 0.00
% 6.14/2.21  Cooper               : 0.00
% 6.14/2.21  Total                : 1.47
% 6.14/2.21  Index Insertion      : 0.00
% 6.14/2.21  Index Deletion       : 0.00
% 6.14/2.21  Index Matching       : 0.00
% 6.14/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
