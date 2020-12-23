%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 9.41s
% Output     : CNFRefutation 9.54s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 235 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 823 expanded)
%              Number of equality atoms :   50 ( 214 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

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

tff(f_114,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_116,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_133,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_197,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_213,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_197])).

tff(c_11713,plain,(
    ! [B_1471,A_1472,C_1473] :
      ( k1_xboole_0 = B_1471
      | k1_relset_1(A_1472,B_1471,C_1473) = A_1472
      | ~ v1_funct_2(C_1473,A_1472,B_1471)
      | ~ m1_subset_1(C_1473,k1_zfmisc_1(k2_zfmisc_1(A_1472,B_1471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11724,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_11713])).

tff(c_11736,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_213,c_11724])).

tff(c_11741,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11736])).

tff(c_132,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_116])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13269,plain,(
    ! [B_1635,C_1636,A_1637] :
      ( k1_funct_1(k5_relat_1(B_1635,C_1636),A_1637) = k1_funct_1(C_1636,k1_funct_1(B_1635,A_1637))
      | ~ r2_hidden(A_1637,k1_relat_1(B_1635))
      | ~ v1_funct_1(C_1636)
      | ~ v1_relat_1(C_1636)
      | ~ v1_funct_1(B_1635)
      | ~ v1_relat_1(B_1635) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13738,plain,(
    ! [B_1697,C_1698,A_1699] :
      ( k1_funct_1(k5_relat_1(B_1697,C_1698),A_1699) = k1_funct_1(C_1698,k1_funct_1(B_1697,A_1699))
      | ~ v1_funct_1(C_1698)
      | ~ v1_relat_1(C_1698)
      | ~ v1_funct_1(B_1697)
      | ~ v1_relat_1(B_1697)
      | v1_xboole_0(k1_relat_1(B_1697))
      | ~ m1_subset_1(A_1699,k1_relat_1(B_1697)) ) ),
    inference(resolution,[status(thm)],[c_10,c_13269])).

tff(c_13750,plain,(
    ! [C_1698,A_1699] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_1698),A_1699) = k1_funct_1(C_1698,k1_funct_1('#skF_5',A_1699))
      | ~ v1_funct_1(C_1698)
      | ~ v1_relat_1(C_1698)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_1699,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11741,c_13738])).

tff(c_13763,plain,(
    ! [C_1698,A_1699] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_1698),A_1699) = k1_funct_1(C_1698,k1_funct_1('#skF_5',A_1699))
      | ~ v1_funct_1(C_1698)
      | ~ v1_relat_1(C_1698)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_1699,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11741,c_132,c_58,c_13750])).

tff(c_13765,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_13763])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13768,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_13765,c_6])).

tff(c_13772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_13768])).

tff(c_13773,plain,(
    ! [C_1698,A_1699] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_1698),A_1699) = k1_funct_1(C_1698,k1_funct_1('#skF_5',A_1699))
      | ~ v1_funct_1(C_1698)
      | ~ v1_relat_1(C_1698)
      | ~ m1_subset_1(A_1699,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_13763])).

tff(c_13335,plain,(
    ! [F_1649,E_1651,B_1653,A_1648,D_1652,C_1650] :
      ( k1_partfun1(A_1648,B_1653,C_1650,D_1652,E_1651,F_1649) = k5_relat_1(E_1651,F_1649)
      | ~ m1_subset_1(F_1649,k1_zfmisc_1(k2_zfmisc_1(C_1650,D_1652)))
      | ~ v1_funct_1(F_1649)
      | ~ m1_subset_1(E_1651,k1_zfmisc_1(k2_zfmisc_1(A_1648,B_1653)))
      | ~ v1_funct_1(E_1651) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_13348,plain,(
    ! [A_1648,B_1653,E_1651] :
      ( k1_partfun1(A_1648,B_1653,'#skF_4','#skF_2',E_1651,'#skF_6') = k5_relat_1(E_1651,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1651,k1_zfmisc_1(k2_zfmisc_1(A_1648,B_1653)))
      | ~ v1_funct_1(E_1651) ) ),
    inference(resolution,[status(thm)],[c_50,c_13335])).

tff(c_13403,plain,(
    ! [A_1657,B_1658,E_1659] :
      ( k1_partfun1(A_1657,B_1658,'#skF_4','#skF_2',E_1659,'#skF_6') = k5_relat_1(E_1659,'#skF_6')
      | ~ m1_subset_1(E_1659,k1_zfmisc_1(k2_zfmisc_1(A_1657,B_1658)))
      | ~ v1_funct_1(E_1659) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13348])).

tff(c_13418,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_13403])).

tff(c_13431,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13418])).

tff(c_214,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_197])).

tff(c_46,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_227,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_46])).

tff(c_13445,plain,(
    ! [D_1660,B_1661,A_1662,C_1663,E_1664] :
      ( k1_partfun1(A_1662,B_1661,B_1661,C_1663,D_1660,E_1664) = k8_funct_2(A_1662,B_1661,C_1663,D_1660,E_1664)
      | k1_xboole_0 = B_1661
      | ~ r1_tarski(k2_relset_1(A_1662,B_1661,D_1660),k1_relset_1(B_1661,C_1663,E_1664))
      | ~ m1_subset_1(E_1664,k1_zfmisc_1(k2_zfmisc_1(B_1661,C_1663)))
      | ~ v1_funct_1(E_1664)
      | ~ m1_subset_1(D_1660,k1_zfmisc_1(k2_zfmisc_1(A_1662,B_1661)))
      | ~ v1_funct_2(D_1660,A_1662,B_1661)
      | ~ v1_funct_1(D_1660) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_13451,plain,(
    ! [A_1662,D_1660] :
      ( k1_partfun1(A_1662,'#skF_4','#skF_4','#skF_2',D_1660,'#skF_6') = k8_funct_2(A_1662,'#skF_4','#skF_2',D_1660,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_1662,'#skF_4',D_1660),k1_relat_1('#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_1660,k1_zfmisc_1(k2_zfmisc_1(A_1662,'#skF_4')))
      | ~ v1_funct_2(D_1660,A_1662,'#skF_4')
      | ~ v1_funct_1(D_1660) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_13445])).

tff(c_13459,plain,(
    ! [A_1662,D_1660] :
      ( k1_partfun1(A_1662,'#skF_4','#skF_4','#skF_2',D_1660,'#skF_6') = k8_funct_2(A_1662,'#skF_4','#skF_2',D_1660,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_1662,'#skF_4',D_1660),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(D_1660,k1_zfmisc_1(k2_zfmisc_1(A_1662,'#skF_4')))
      | ~ v1_funct_2(D_1660,A_1662,'#skF_4')
      | ~ v1_funct_1(D_1660) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_13451])).

tff(c_14360,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13459])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_96,plain,(
    ! [A_65] : r1_tarski(k1_xboole_0,A_65) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_58,A_59] :
      ( ~ r1_tarski(B_58,A_59)
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_96,c_76])).

tff(c_14386,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14360,c_101])).

tff(c_14393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14386])).

tff(c_14462,plain,(
    ! [A_1772,D_1773] :
      ( k1_partfun1(A_1772,'#skF_4','#skF_4','#skF_2',D_1773,'#skF_6') = k8_funct_2(A_1772,'#skF_4','#skF_2',D_1773,'#skF_6')
      | ~ r1_tarski(k2_relset_1(A_1772,'#skF_4',D_1773),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(D_1773,k1_zfmisc_1(k2_zfmisc_1(A_1772,'#skF_4')))
      | ~ v1_funct_2(D_1773,A_1772,'#skF_4')
      | ~ v1_funct_1(D_1773) ) ),
    inference(splitRight,[status(thm)],[c_13459])).

tff(c_14465,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_227,c_14462])).

tff(c_14468,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_13431,c_14465])).

tff(c_42,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_14469,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14468,c_42])).

tff(c_14476,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13773,c_14469])).

tff(c_14483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_133,c_52,c_14476])).

tff(c_14484,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11736])).

tff(c_14497,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14484,c_101])).

tff(c_14504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14497])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.41/3.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.76  
% 9.41/3.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.77  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 9.41/3.77  
% 9.41/3.77  %Foreground sorts:
% 9.41/3.77  
% 9.41/3.77  
% 9.41/3.77  %Background operators:
% 9.41/3.77  
% 9.41/3.77  
% 9.41/3.77  %Foreground operators:
% 9.41/3.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.41/3.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.41/3.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.41/3.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.41/3.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.41/3.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.41/3.77  tff('#skF_7', type, '#skF_7': $i).
% 9.41/3.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.77  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.77  tff('#skF_5', type, '#skF_5': $i).
% 9.41/3.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.41/3.77  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 9.41/3.77  tff('#skF_6', type, '#skF_6': $i).
% 9.41/3.77  tff('#skF_2', type, '#skF_2': $i).
% 9.41/3.77  tff('#skF_3', type, '#skF_3': $i).
% 9.41/3.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.41/3.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.41/3.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.41/3.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.41/3.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.41/3.77  tff('#skF_4', type, '#skF_4': $i).
% 9.41/3.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.41/3.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.41/3.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.41/3.77  
% 9.54/3.78  tff(f_149, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 9.54/3.78  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.54/3.78  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.54/3.78  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.54/3.78  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.54/3.78  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 9.54/3.78  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.54/3.78  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.54/3.78  tff(f_96, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 9.54/3.78  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.54/3.78  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.54/3.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.54/3.78  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.54/3.78  tff(c_60, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_48, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_116, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.54/3.78  tff(c_133, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_116])).
% 9.54/3.78  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_56, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_197, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.54/3.78  tff(c_213, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_197])).
% 9.54/3.78  tff(c_11713, plain, (![B_1471, A_1472, C_1473]: (k1_xboole_0=B_1471 | k1_relset_1(A_1472, B_1471, C_1473)=A_1472 | ~v1_funct_2(C_1473, A_1472, B_1471) | ~m1_subset_1(C_1473, k1_zfmisc_1(k2_zfmisc_1(A_1472, B_1471))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.54/3.78  tff(c_11724, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_11713])).
% 9.54/3.78  tff(c_11736, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_213, c_11724])).
% 9.54/3.78  tff(c_11741, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_11736])).
% 9.54/3.78  tff(c_132, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_116])).
% 9.54/3.78  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.54/3.78  tff(c_13269, plain, (![B_1635, C_1636, A_1637]: (k1_funct_1(k5_relat_1(B_1635, C_1636), A_1637)=k1_funct_1(C_1636, k1_funct_1(B_1635, A_1637)) | ~r2_hidden(A_1637, k1_relat_1(B_1635)) | ~v1_funct_1(C_1636) | ~v1_relat_1(C_1636) | ~v1_funct_1(B_1635) | ~v1_relat_1(B_1635))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.54/3.78  tff(c_13738, plain, (![B_1697, C_1698, A_1699]: (k1_funct_1(k5_relat_1(B_1697, C_1698), A_1699)=k1_funct_1(C_1698, k1_funct_1(B_1697, A_1699)) | ~v1_funct_1(C_1698) | ~v1_relat_1(C_1698) | ~v1_funct_1(B_1697) | ~v1_relat_1(B_1697) | v1_xboole_0(k1_relat_1(B_1697)) | ~m1_subset_1(A_1699, k1_relat_1(B_1697)))), inference(resolution, [status(thm)], [c_10, c_13269])).
% 9.54/3.78  tff(c_13750, plain, (![C_1698, A_1699]: (k1_funct_1(k5_relat_1('#skF_5', C_1698), A_1699)=k1_funct_1(C_1698, k1_funct_1('#skF_5', A_1699)) | ~v1_funct_1(C_1698) | ~v1_relat_1(C_1698) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_1699, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11741, c_13738])).
% 9.54/3.78  tff(c_13763, plain, (![C_1698, A_1699]: (k1_funct_1(k5_relat_1('#skF_5', C_1698), A_1699)=k1_funct_1(C_1698, k1_funct_1('#skF_5', A_1699)) | ~v1_funct_1(C_1698) | ~v1_relat_1(C_1698) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_1699, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11741, c_132, c_58, c_13750])).
% 9.54/3.78  tff(c_13765, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_13763])).
% 9.54/3.78  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.54/3.78  tff(c_13768, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_13765, c_6])).
% 9.54/3.78  tff(c_13772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_13768])).
% 9.54/3.78  tff(c_13773, plain, (![C_1698, A_1699]: (k1_funct_1(k5_relat_1('#skF_5', C_1698), A_1699)=k1_funct_1(C_1698, k1_funct_1('#skF_5', A_1699)) | ~v1_funct_1(C_1698) | ~v1_relat_1(C_1698) | ~m1_subset_1(A_1699, '#skF_3'))), inference(splitRight, [status(thm)], [c_13763])).
% 9.54/3.78  tff(c_13335, plain, (![F_1649, E_1651, B_1653, A_1648, D_1652, C_1650]: (k1_partfun1(A_1648, B_1653, C_1650, D_1652, E_1651, F_1649)=k5_relat_1(E_1651, F_1649) | ~m1_subset_1(F_1649, k1_zfmisc_1(k2_zfmisc_1(C_1650, D_1652))) | ~v1_funct_1(F_1649) | ~m1_subset_1(E_1651, k1_zfmisc_1(k2_zfmisc_1(A_1648, B_1653))) | ~v1_funct_1(E_1651))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.54/3.78  tff(c_13348, plain, (![A_1648, B_1653, E_1651]: (k1_partfun1(A_1648, B_1653, '#skF_4', '#skF_2', E_1651, '#skF_6')=k5_relat_1(E_1651, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1651, k1_zfmisc_1(k2_zfmisc_1(A_1648, B_1653))) | ~v1_funct_1(E_1651))), inference(resolution, [status(thm)], [c_50, c_13335])).
% 9.54/3.78  tff(c_13403, plain, (![A_1657, B_1658, E_1659]: (k1_partfun1(A_1657, B_1658, '#skF_4', '#skF_2', E_1659, '#skF_6')=k5_relat_1(E_1659, '#skF_6') | ~m1_subset_1(E_1659, k1_zfmisc_1(k2_zfmisc_1(A_1657, B_1658))) | ~v1_funct_1(E_1659))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13348])).
% 9.54/3.78  tff(c_13418, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_13403])).
% 9.54/3.78  tff(c_13431, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13418])).
% 9.54/3.78  tff(c_214, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_197])).
% 9.54/3.78  tff(c_46, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_227, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_46])).
% 9.54/3.78  tff(c_13445, plain, (![D_1660, B_1661, A_1662, C_1663, E_1664]: (k1_partfun1(A_1662, B_1661, B_1661, C_1663, D_1660, E_1664)=k8_funct_2(A_1662, B_1661, C_1663, D_1660, E_1664) | k1_xboole_0=B_1661 | ~r1_tarski(k2_relset_1(A_1662, B_1661, D_1660), k1_relset_1(B_1661, C_1663, E_1664)) | ~m1_subset_1(E_1664, k1_zfmisc_1(k2_zfmisc_1(B_1661, C_1663))) | ~v1_funct_1(E_1664) | ~m1_subset_1(D_1660, k1_zfmisc_1(k2_zfmisc_1(A_1662, B_1661))) | ~v1_funct_2(D_1660, A_1662, B_1661) | ~v1_funct_1(D_1660))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.54/3.78  tff(c_13451, plain, (![A_1662, D_1660]: (k1_partfun1(A_1662, '#skF_4', '#skF_4', '#skF_2', D_1660, '#skF_6')=k8_funct_2(A_1662, '#skF_4', '#skF_2', D_1660, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_1662, '#skF_4', D_1660), k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_1660, k1_zfmisc_1(k2_zfmisc_1(A_1662, '#skF_4'))) | ~v1_funct_2(D_1660, A_1662, '#skF_4') | ~v1_funct_1(D_1660))), inference(superposition, [status(thm), theory('equality')], [c_214, c_13445])).
% 9.54/3.78  tff(c_13459, plain, (![A_1662, D_1660]: (k1_partfun1(A_1662, '#skF_4', '#skF_4', '#skF_2', D_1660, '#skF_6')=k8_funct_2(A_1662, '#skF_4', '#skF_2', D_1660, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_1662, '#skF_4', D_1660), k1_relat_1('#skF_6')) | ~m1_subset_1(D_1660, k1_zfmisc_1(k2_zfmisc_1(A_1662, '#skF_4'))) | ~v1_funct_2(D_1660, A_1662, '#skF_4') | ~v1_funct_1(D_1660))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_13451])).
% 9.54/3.78  tff(c_14360, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13459])).
% 9.54/3.78  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.54/3.78  tff(c_79, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.54/3.78  tff(c_96, plain, (![A_65]: (r1_tarski(k1_xboole_0, A_65))), inference(resolution, [status(thm)], [c_8, c_79])).
% 9.54/3.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.54/3.78  tff(c_72, plain, (![B_58, A_59]: (~r1_tarski(B_58, A_59) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.54/3.78  tff(c_76, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_72])).
% 9.54/3.78  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_96, c_76])).
% 9.54/3.78  tff(c_14386, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14360, c_101])).
% 9.54/3.78  tff(c_14393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_14386])).
% 9.54/3.78  tff(c_14462, plain, (![A_1772, D_1773]: (k1_partfun1(A_1772, '#skF_4', '#skF_4', '#skF_2', D_1773, '#skF_6')=k8_funct_2(A_1772, '#skF_4', '#skF_2', D_1773, '#skF_6') | ~r1_tarski(k2_relset_1(A_1772, '#skF_4', D_1773), k1_relat_1('#skF_6')) | ~m1_subset_1(D_1773, k1_zfmisc_1(k2_zfmisc_1(A_1772, '#skF_4'))) | ~v1_funct_2(D_1773, A_1772, '#skF_4') | ~v1_funct_1(D_1773))), inference(splitRight, [status(thm)], [c_13459])).
% 9.54/3.78  tff(c_14465, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_227, c_14462])).
% 9.54/3.78  tff(c_14468, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_13431, c_14465])).
% 9.54/3.78  tff(c_42, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.54/3.78  tff(c_14469, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_14468, c_42])).
% 9.54/3.78  tff(c_14476, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13773, c_14469])).
% 9.54/3.78  tff(c_14483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_133, c_52, c_14476])).
% 9.54/3.78  tff(c_14484, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11736])).
% 9.54/3.78  tff(c_14497, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14484, c_101])).
% 9.54/3.78  tff(c_14504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_14497])).
% 9.54/3.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.54/3.78  
% 9.54/3.78  Inference rules
% 9.54/3.78  ----------------------
% 9.54/3.78  #Ref     : 0
% 9.54/3.78  #Sup     : 2692
% 9.54/3.78  #Fact    : 0
% 9.54/3.78  #Define  : 0
% 9.54/3.78  #Split   : 46
% 9.54/3.78  #Chain   : 0
% 9.54/3.78  #Close   : 0
% 9.54/3.78  
% 9.54/3.78  Ordering : KBO
% 9.54/3.78  
% 9.54/3.78  Simplification rules
% 9.54/3.78  ----------------------
% 9.54/3.78  #Subsume      : 409
% 9.54/3.78  #Demod        : 2318
% 9.54/3.78  #Tautology    : 752
% 9.54/3.78  #SimpNegUnit  : 143
% 9.54/3.78  #BackRed      : 553
% 9.54/3.78  
% 9.54/3.78  #Partial instantiations: 0
% 9.54/3.78  #Strategies tried      : 1
% 9.54/3.78  
% 9.54/3.78  Timing (in seconds)
% 9.54/3.78  ----------------------
% 9.54/3.79  Preprocessing        : 0.35
% 9.54/3.79  Parsing              : 0.18
% 9.54/3.79  CNF conversion       : 0.03
% 9.54/3.79  Main loop            : 2.67
% 9.54/3.79  Inferencing          : 0.79
% 9.54/3.79  Reduction            : 0.77
% 9.54/3.79  Demodulation         : 0.51
% 9.54/3.79  BG Simplification    : 0.11
% 9.54/3.79  Subsumption          : 0.78
% 9.54/3.79  Abstraction          : 0.16
% 9.54/3.79  MUC search           : 0.00
% 9.54/3.79  Cooper               : 0.00
% 9.54/3.79  Total                : 3.06
% 9.54/3.79  Index Insertion      : 0.00
% 9.54/3.79  Index Deletion       : 0.00
% 9.54/3.79  Index Matching       : 0.00
% 9.54/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
