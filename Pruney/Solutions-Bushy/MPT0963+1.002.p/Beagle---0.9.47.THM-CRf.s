%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0963+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:08 EST 2020

% Result     : Theorem 12.31s
% Output     : CNFRefutation 12.65s
% Verified   : 
% Statistics : Number of formulae       :  231 (2201 expanded)
%              Number of leaves         :   42 ( 720 expanded)
%              Depth                    :   19
%              Number of atoms          :  420 (5361 expanded)
%              Number of equality atoms :   54 ( 746 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k1_relat_1(C) = A
            & ! [D] :
                ( r2_hidden(D,A)
               => r2_hidden(k1_funct_1(C,D),B) ) )
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_49,axiom,(
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

tff(f_76,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_79,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_72,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),A_8)
      | r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23941,plain,(
    ! [A_1260,B_1261] :
      ( ~ r2_hidden('#skF_1'(A_1260,B_1261),B_1261)
      | r1_tarski(A_1260,B_1261) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_23951,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_20,c_23941])).

tff(c_68,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_70,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_29731,plain,(
    ! [A_1710,C_1711] :
      ( r2_hidden('#skF_5'(A_1710,k2_relat_1(A_1710),C_1711),k1_relat_1(A_1710))
      | ~ r2_hidden(C_1711,k2_relat_1(A_1710))
      | ~ v1_funct_1(A_1710)
      | ~ v1_relat_1(A_1710) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_29744,plain,(
    ! [C_1711] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1711),'#skF_7')
      | ~ r2_hidden(C_1711,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_29731])).

tff(c_29750,plain,(
    ! [C_1711] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1711),'#skF_7')
      | ~ r2_hidden(C_1711,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_29744])).

tff(c_29863,plain,(
    ! [A_1722,C_1723] :
      ( k1_funct_1(A_1722,'#skF_5'(A_1722,k2_relat_1(A_1722),C_1723)) = C_1723
      | ~ r2_hidden(C_1723,k2_relat_1(A_1722))
      | ~ v1_funct_1(A_1722)
      | ~ v1_relat_1(A_1722) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ! [D_77] :
      ( r2_hidden(k1_funct_1('#skF_9',D_77),'#skF_8')
      | ~ r2_hidden(D_77,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_29877,plain,(
    ! [C_1723] :
      ( r2_hidden(C_1723,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1723),'#skF_7')
      | ~ r2_hidden(C_1723,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29863,c_66])).

tff(c_30081,plain,(
    ! [C_1738] :
      ( r2_hidden(C_1738,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1738),'#skF_7')
      | ~ r2_hidden(C_1738,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_29877])).

tff(c_30092,plain,(
    ! [C_1739] :
      ( r2_hidden(C_1739,'#skF_8')
      | ~ r2_hidden(C_1739,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_29750,c_30081])).

tff(c_30303,plain,(
    ! [B_1748] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_1748),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_9'),B_1748) ) ),
    inference(resolution,[status(thm)],[c_20,c_30092])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_1'(A_8,B_9),B_9)
      | r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30317,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_30303,c_18])).

tff(c_30332,plain,(
    ! [C_1749,A_1750,B_1751] :
      ( m1_subset_1(C_1749,k1_zfmisc_1(k2_zfmisc_1(A_1750,B_1751)))
      | ~ r1_tarski(k2_relat_1(C_1749),B_1751)
      | ~ r1_tarski(k1_relat_1(C_1749),A_1750)
      | ~ v1_relat_1(C_1749) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_96,plain,(
    ! [D_82] :
      ( r2_hidden(k1_funct_1('#skF_9',D_82),'#skF_8')
      | ~ r2_hidden(D_82,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_60,plain,(
    ! [B_73,A_72] :
      ( ~ v1_xboole_0(B_73)
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_100,plain,(
    ! [D_82] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(D_82,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_96,c_60])).

tff(c_101,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_130,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden('#skF_1'(A_96,B_97),B_97)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_20,c_130])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64])).

tff(c_129,plain,(
    ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_15424,plain,(
    ! [A_959,C_960] :
      ( r2_hidden('#skF_5'(A_959,k2_relat_1(A_959),C_960),k1_relat_1(A_959))
      | ~ r2_hidden(C_960,k2_relat_1(A_959))
      | ~ v1_funct_1(A_959)
      | ~ v1_relat_1(A_959) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15437,plain,(
    ! [C_960] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_960),'#skF_7')
      | ~ r2_hidden(C_960,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_15424])).

tff(c_15443,plain,(
    ! [C_960] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_960),'#skF_7')
      | ~ r2_hidden(C_960,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_15437])).

tff(c_15696,plain,(
    ! [A_983,C_984] :
      ( k1_funct_1(A_983,'#skF_5'(A_983,k2_relat_1(A_983),C_984)) = C_984
      | ~ r2_hidden(C_984,k2_relat_1(A_983))
      | ~ v1_funct_1(A_983)
      | ~ v1_relat_1(A_983) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_15710,plain,(
    ! [C_984] :
      ( r2_hidden(C_984,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_984),'#skF_7')
      | ~ r2_hidden(C_984,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15696,c_66])).

tff(c_15777,plain,(
    ! [C_991] :
      ( r2_hidden(C_991,'#skF_8')
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_991),'#skF_7')
      | ~ r2_hidden(C_991,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_15710])).

tff(c_15795,plain,(
    ! [C_992] :
      ( r2_hidden(C_992,'#skF_8')
      | ~ r2_hidden(C_992,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_15443,c_15777])).

tff(c_15992,plain,(
    ! [B_1001] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_9'),B_1001),'#skF_8')
      | r1_tarski(k2_relat_1('#skF_9'),B_1001) ) ),
    inference(resolution,[status(thm)],[c_20,c_15795])).

tff(c_16006,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_15992,c_18])).

tff(c_15376,plain,(
    ! [C_954,A_955,B_956] :
      ( m1_subset_1(C_954,k1_zfmisc_1(k2_zfmisc_1(A_955,B_956)))
      | ~ r1_tarski(k2_relat_1(C_954),B_956)
      | ~ r1_tarski(k1_relat_1(C_954),A_955)
      | ~ v1_relat_1(C_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22453,plain,(
    ! [C_1227,A_1228,B_1229] :
      ( r1_tarski(C_1227,k2_zfmisc_1(A_1228,B_1229))
      | ~ r1_tarski(k2_relat_1(C_1227),B_1229)
      | ~ r1_tarski(k1_relat_1(C_1227),A_1228)
      | ~ v1_relat_1(C_1227) ) ),
    inference(resolution,[status(thm)],[c_15376,c_52])).

tff(c_22457,plain,(
    ! [A_1228] :
      ( r1_tarski('#skF_9',k2_zfmisc_1(A_1228,'#skF_8'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),A_1228)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16006,c_22453])).

tff(c_22470,plain,(
    ! [A_1230] :
      ( r1_tarski('#skF_9',k2_zfmisc_1(A_1230,'#skF_8'))
      | ~ r1_tarski('#skF_7',A_1230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_22457])).

tff(c_54,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(A_66,k1_zfmisc_1(B_67))
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12793,plain,(
    ! [A_794,B_795,C_796] :
      ( k1_relset_1(A_794,B_795,C_796) = k1_relat_1(C_796)
      | ~ m1_subset_1(C_796,k1_zfmisc_1(k2_zfmisc_1(A_794,B_795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12809,plain,(
    ! [A_794,B_795,A_66] :
      ( k1_relset_1(A_794,B_795,A_66) = k1_relat_1(A_66)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_794,B_795)) ) ),
    inference(resolution,[status(thm)],[c_54,c_12793])).

tff(c_22491,plain,(
    ! [A_1230] :
      ( k1_relset_1(A_1230,'#skF_8','#skF_9') = k1_relat_1('#skF_9')
      | ~ r1_tarski('#skF_7',A_1230) ) ),
    inference(resolution,[status(thm)],[c_22470,c_12809])).

tff(c_22519,plain,(
    ! [A_1231] :
      ( k1_relset_1(A_1231,'#skF_8','#skF_9') = '#skF_7'
      | ~ r1_tarski('#skF_7',A_1231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22491])).

tff(c_22528,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_140,c_22519])).

tff(c_48,plain,(
    ! [C_63,A_61,B_62] :
      ( m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ r1_tarski(k2_relat_1(C_63),B_62)
      | ~ r1_tarski(k1_relat_1(C_63),A_61)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    ! [A_53,B_54,C_55] :
      ( m1_subset_1(k1_relset_1(A_53,B_54,C_55),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22538,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22528,c_40])).

tff(c_23659,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_22538])).

tff(c_23775,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_23659])).

tff(c_23782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_140,c_68,c_16006,c_23775])).

tff(c_23784,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_22538])).

tff(c_10,plain,(
    ! [B_6,C_7,A_5] :
      ( k1_xboole_0 = B_6
      | v1_funct_2(C_7,A_5,B_6)
      | k1_relset_1(A_5,B_6,C_7) != A_5
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_23800,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2('#skF_9','#skF_7','#skF_8')
    | k1_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_23784,c_10])).

tff(c_23821,plain,
    ( k1_xboole_0 = '#skF_8'
    | v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22528,c_23800])).

tff(c_23822,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_23821])).

tff(c_161,plain,(
    ! [C_104,B_105,A_106] :
      ( r2_hidden(C_104,B_105)
      | ~ r2_hidden(C_104,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,(
    ! [D_77,B_105] :
      ( r2_hidden(k1_funct_1('#skF_9',D_77),B_105)
      | ~ r1_tarski('#skF_8',B_105)
      | ~ r2_hidden(D_77,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_161])).

tff(c_42,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    ! [A_78] :
      ( k1_xboole_0 = A_78
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_83,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_42])).

tff(c_3127,plain,(
    ! [C_278,B_279,A_280] :
      ( v1_xboole_0(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(B_279,A_280)))
      | ~ v1_xboole_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3204,plain,(
    ! [A_291,A_292,B_293] :
      ( v1_xboole_0(A_291)
      | ~ v1_xboole_0(A_292)
      | ~ r1_tarski(A_291,k2_zfmisc_1(B_293,A_292)) ) ),
    inference(resolution,[status(thm)],[c_54,c_3127])).

tff(c_3242,plain,(
    ! [B_295,A_296] :
      ( v1_xboole_0(k2_zfmisc_1(B_295,A_296))
      | ~ v1_xboole_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_140,c_3204])).

tff(c_58,plain,(
    ! [A_71] :
      ( k1_xboole_0 = A_71
      | ~ v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3250,plain,(
    ! [B_297,A_298] :
      ( k2_zfmisc_1(B_297,A_298) = k1_xboole_0
      | ~ v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_3242,c_58])).

tff(c_3261,plain,(
    ! [B_299] : k2_zfmisc_1(B_299,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_3250])).

tff(c_44,plain,(
    ! [A_56] : m1_subset_1('#skF_6'(A_56),A_56) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3154,plain,(
    ! [B_283,A_284] :
      ( v1_xboole_0('#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_283,A_284))))
      | ~ v1_xboole_0(A_284) ) ),
    inference(resolution,[status(thm)],[c_44,c_3127])).

tff(c_3162,plain,(
    ! [B_285,A_286] :
      ( '#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_285,A_286))) = k1_xboole_0
      | ~ v1_xboole_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_3154,c_58])).

tff(c_3180,plain,(
    ! [B_285,A_286] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(B_285,A_286)))
      | ~ v1_xboole_0(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_44])).

tff(c_3272,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3261,c_3180])).

tff(c_3293,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3272])).

tff(c_56,plain,(
    ! [C_70,B_69,A_68] :
      ( ~ v1_xboole_0(C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12745,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3293,c_56])).

tff(c_12754,plain,(
    ! [A_792] : ~ r2_hidden(A_792,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_12745])).

tff(c_12767,plain,(
    ! [D_77] :
      ( ~ r1_tarski('#skF_8',k1_xboole_0)
      | ~ r2_hidden(D_77,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_170,c_12754])).

tff(c_12865,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12767])).

tff(c_23892,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23822,c_12865])).

tff(c_23905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_23892])).

tff(c_23907,plain,(
    r1_tarski('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12767])).

tff(c_3136,plain,(
    ! [A_66,A_280,B_279] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(A_280)
      | ~ r1_tarski(A_66,k2_zfmisc_1(B_279,A_280)) ) ),
    inference(resolution,[status(thm)],[c_54,c_3127])).

tff(c_3269,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3261,c_3136])).

tff(c_3291,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3269])).

tff(c_23921,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_23907,c_3291])).

tff(c_23930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_23921])).

tff(c_23931,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_30355,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30332,c_23931])).

tff(c_30380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_23951,c_68,c_30317,c_30355])).

tff(c_30382,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_32125,plain,(
    ! [A_1910,B_1911] :
      ( ~ r2_hidden('#skF_1'(A_1910,B_1911),B_1911)
      | r1_tarski(A_1910,B_1911) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32135,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(resolution,[status(thm)],[c_20,c_32125])).

tff(c_32180,plain,(
    ! [C_1926,B_1927,A_1928] :
      ( v1_xboole_0(C_1926)
      | ~ m1_subset_1(C_1926,k1_zfmisc_1(k2_zfmisc_1(B_1927,A_1928)))
      | ~ v1_xboole_0(A_1928) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32266,plain,(
    ! [A_1940,A_1941,B_1942] :
      ( v1_xboole_0(A_1940)
      | ~ v1_xboole_0(A_1941)
      | ~ r1_tarski(A_1940,k2_zfmisc_1(B_1942,A_1941)) ) ),
    inference(resolution,[status(thm)],[c_54,c_32180])).

tff(c_32293,plain,(
    ! [B_1943,A_1944] :
      ( v1_xboole_0(k2_zfmisc_1(B_1943,A_1944))
      | ~ v1_xboole_0(A_1944) ) ),
    inference(resolution,[status(thm)],[c_32135,c_32266])).

tff(c_30386,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30382,c_58])).

tff(c_30389,plain,(
    ! [A_71] :
      ( A_71 = '#skF_8'
      | ~ v1_xboole_0(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30386,c_58])).

tff(c_32301,plain,(
    ! [B_1945,A_1946] :
      ( k2_zfmisc_1(B_1945,A_1946) = '#skF_8'
      | ~ v1_xboole_0(A_1946) ) ),
    inference(resolution,[status(thm)],[c_32293,c_30389])).

tff(c_32310,plain,(
    ! [B_1945] : k2_zfmisc_1(B_1945,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30382,c_32301])).

tff(c_32070,plain,(
    ! [A_1905,B_1906] :
      ( r2_hidden(A_1905,B_1906)
      | v1_xboole_0(B_1906)
      | ~ m1_subset_1(A_1905,B_1906) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30381,plain,(
    ! [D_82] : ~ r2_hidden(D_82,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_32078,plain,(
    ! [A_1905] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_1905,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_32070,c_30381])).

tff(c_32081,plain,(
    ! [A_1907] : ~ m1_subset_1(A_1907,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32078])).

tff(c_32086,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_44,c_32081])).

tff(c_32087,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_32078])).

tff(c_32094,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32087,c_30389])).

tff(c_30424,plain,(
    ! [A_1763,B_1764] :
      ( r2_hidden('#skF_1'(A_1763,B_1764),A_1763)
      | r1_tarski(A_1763,B_1764) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30436,plain,(
    ! [A_1763] : r1_tarski(A_1763,A_1763) ),
    inference(resolution,[status(thm)],[c_30424,c_18])).

tff(c_30527,plain,(
    ! [C_1782,B_1783,A_1784] :
      ( v1_xboole_0(C_1782)
      | ~ m1_subset_1(C_1782,k1_zfmisc_1(k2_zfmisc_1(B_1783,A_1784)))
      | ~ v1_xboole_0(A_1784) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30621,plain,(
    ! [A_1801,A_1802,B_1803] :
      ( v1_xboole_0(A_1801)
      | ~ v1_xboole_0(A_1802)
      | ~ r1_tarski(A_1801,k2_zfmisc_1(B_1803,A_1802)) ) ),
    inference(resolution,[status(thm)],[c_54,c_30527])).

tff(c_30663,plain,(
    ! [B_1807,A_1808] :
      ( v1_xboole_0(k2_zfmisc_1(B_1807,A_1808))
      | ~ v1_xboole_0(A_1808) ) ),
    inference(resolution,[status(thm)],[c_30436,c_30621])).

tff(c_30671,plain,(
    ! [B_1809,A_1810] :
      ( k2_zfmisc_1(B_1809,A_1810) = '#skF_8'
      | ~ v1_xboole_0(A_1810) ) ),
    inference(resolution,[status(thm)],[c_30663,c_30389])).

tff(c_30681,plain,(
    ! [B_1811] : k2_zfmisc_1(B_1811,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30382,c_30671])).

tff(c_30546,plain,(
    ! [B_1790,A_1791] :
      ( v1_xboole_0('#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_1790,A_1791))))
      | ~ v1_xboole_0(A_1791) ) ),
    inference(resolution,[status(thm)],[c_44,c_30527])).

tff(c_30580,plain,(
    ! [B_1797,A_1798] :
      ( '#skF_6'(k1_zfmisc_1(k2_zfmisc_1(B_1797,A_1798))) = '#skF_8'
      | ~ v1_xboole_0(A_1798) ) ),
    inference(resolution,[status(thm)],[c_30546,c_30389])).

tff(c_30598,plain,(
    ! [B_1797,A_1798] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_1797,A_1798)))
      | ~ v1_xboole_0(A_1798) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30580,c_44])).

tff(c_30695,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_30681,c_30598])).

tff(c_30713,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30382,c_30695])).

tff(c_30680,plain,(
    ! [B_1809] : k2_zfmisc_1(B_1809,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30382,c_30671])).

tff(c_46,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30689,plain,(
    ! [B_1811,C_60] :
      ( k1_relset_1(B_1811,'#skF_8',C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30681,c_46])).

tff(c_30872,plain,(
    ! [B_1820] : k1_relset_1(B_1820,'#skF_8','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30713,c_30689])).

tff(c_30877,plain,(
    ! [B_1820] :
      ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(B_1820))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_1820,'#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30872,c_40])).

tff(c_30884,plain,(
    ! [B_1821] : m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(B_1821)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30713,c_30680,c_30877])).

tff(c_2,plain,(
    ! [C_4,B_2,A_1] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(B_2,A_1)))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30704,plain,(
    ! [C_4] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1('#skF_8'))
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30681,c_2])).

tff(c_30719,plain,(
    ! [C_4] :
      ( v1_xboole_0(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30382,c_30704])).

tff(c_30905,plain,(
    v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_30884,c_30719])).

tff(c_30920,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30905,c_30389])).

tff(c_30882,plain,(
    ! [B_1820] : m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1(B_1820)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30713,c_30680,c_30877])).

tff(c_30932,plain,(
    ! [B_1822] : m1_subset_1('#skF_8',k1_zfmisc_1(B_1822)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30920,c_30882])).

tff(c_30943,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30932,c_46])).

tff(c_30958,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30920,c_30943])).

tff(c_30922,plain,(
    ! [B_1820] : m1_subset_1('#skF_8',k1_zfmisc_1(B_1820)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30920,c_30882])).

tff(c_8,plain,(
    ! [C_7,B_6] :
      ( v1_funct_2(C_7,k1_xboole_0,B_6)
      | k1_relset_1(k1_xboole_0,B_6,C_7) != k1_xboole_0
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31223,plain,(
    ! [C_1845,B_1846] :
      ( v1_funct_2(C_1845,'#skF_8',B_1846)
      | k1_relset_1('#skF_8',B_1846,C_1845) != '#skF_8'
      | ~ m1_subset_1(C_1845,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_1846))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30386,c_30386,c_30386,c_30386,c_8])).

tff(c_31235,plain,(
    ! [B_1846] :
      ( v1_funct_2('#skF_8','#skF_8',B_1846)
      | k1_relset_1('#skF_8',B_1846,'#skF_8') != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_30922,c_31223])).

tff(c_31254,plain,(
    ! [B_1846] : v1_funct_2('#skF_8','#skF_8',B_1846) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30958,c_31235])).

tff(c_30442,plain,(
    ! [A_1769,B_1770] :
      ( r2_hidden(A_1769,B_1770)
      | v1_xboole_0(B_1770)
      | ~ m1_subset_1(A_1769,B_1770) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30455,plain,(
    ! [A_1769] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_1769,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30442,c_30381])).

tff(c_30458,plain,(
    ! [A_1771] : ~ m1_subset_1(A_1771,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_30455])).

tff(c_30463,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_44,c_30458])).

tff(c_30464,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_30455])).

tff(c_30478,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30464,c_30389])).

tff(c_30437,plain,(
    ! [B_1764] : r1_tarski('#skF_7',B_1764) ),
    inference(resolution,[status(thm)],[c_30424,c_30381])).

tff(c_30480,plain,(
    ! [B_1764] : r1_tarski('#skF_8',B_1764) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30478,c_30437])).

tff(c_30483,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30478,c_68])).

tff(c_30482,plain,(
    ! [D_82] : ~ r2_hidden(D_82,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30478,c_30381])).

tff(c_31773,plain,(
    ! [A_1882,C_1883] :
      ( r2_hidden('#skF_5'(A_1882,k2_relat_1(A_1882),C_1883),k1_relat_1(A_1882))
      | ~ r2_hidden(C_1883,k2_relat_1(A_1882))
      | ~ v1_funct_1(A_1882)
      | ~ v1_relat_1(A_1882) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_31786,plain,(
    ! [C_1883] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1883),'#skF_8')
      | ~ r2_hidden(C_1883,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30483,c_31773])).

tff(c_31792,plain,(
    ! [C_1883] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_1883),'#skF_8')
      | ~ r2_hidden(C_1883,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_31786])).

tff(c_31794,plain,(
    ! [C_1884] : ~ r2_hidden(C_1884,k2_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_30482,c_31792])).

tff(c_31817,plain,(
    ! [B_1885] : r1_tarski(k2_relat_1('#skF_9'),B_1885) ),
    inference(resolution,[status(thm)],[c_20,c_31794])).

tff(c_30536,plain,(
    ! [A_66,A_1784,B_1783] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0(A_1784)
      | ~ r1_tarski(A_66,k2_zfmisc_1(B_1783,A_1784)) ) ),
    inference(resolution,[status(thm)],[c_54,c_30527])).

tff(c_30692,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ v1_xboole_0('#skF_8')
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30681,c_30536])).

tff(c_30711,plain,(
    ! [A_66] :
      ( v1_xboole_0(A_66)
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30382,c_30692])).

tff(c_31845,plain,(
    v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_31817,c_30711])).

tff(c_31876,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_31845,c_30389])).

tff(c_31902,plain,(
    ! [C_1886,A_1887,B_1888] :
      ( m1_subset_1(C_1886,k1_zfmisc_1(k2_zfmisc_1(A_1887,B_1888)))
      | ~ r1_tarski(k2_relat_1(C_1886),B_1888)
      | ~ r1_tarski(k1_relat_1(C_1886),A_1887)
      | ~ v1_relat_1(C_1886) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_31948,plain,(
    ! [C_1889,B_1890] :
      ( m1_subset_1(C_1889,k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1(C_1889),'#skF_8')
      | ~ r1_tarski(k1_relat_1(C_1889),B_1890)
      | ~ v1_relat_1(C_1889) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30680,c_31902])).

tff(c_31950,plain,(
    ! [B_1890] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski('#skF_8','#skF_8')
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_1890)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31876,c_31948])).

tff(c_31955,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30480,c_30483,c_30436,c_31950])).

tff(c_31977,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_31955,c_30719])).

tff(c_32012,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_31977,c_30389])).

tff(c_30399,plain,(
    ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_30481,plain,(
    ~ v1_funct_2('#skF_9','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30478,c_30399])).

tff(c_32016,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32012,c_30481])).

tff(c_32024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31254,c_32016])).

tff(c_32025,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_32098,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32094,c_32025])).

tff(c_32326,plain,(
    ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32310,c_32098])).

tff(c_32054,plain,(
    ! [A_1900,B_1901] :
      ( r2_hidden('#skF_1'(A_1900,B_1901),A_1900)
      | r1_tarski(A_1900,B_1901) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32062,plain,(
    ! [B_1901] : r1_tarski('#skF_7',B_1901) ),
    inference(resolution,[status(thm)],[c_32054,c_30381])).

tff(c_32096,plain,(
    ! [B_1901] : r1_tarski('#skF_8',B_1901) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32094,c_32062])).

tff(c_32101,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32094,c_68])).

tff(c_32100,plain,(
    ! [D_82] : ~ r2_hidden(D_82,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32094,c_30381])).

tff(c_34114,plain,(
    ! [A_2061,C_2062] :
      ( r2_hidden('#skF_5'(A_2061,k2_relat_1(A_2061),C_2062),k1_relat_1(A_2061))
      | ~ r2_hidden(C_2062,k2_relat_1(A_2061))
      | ~ v1_funct_1(A_2061)
      | ~ v1_relat_1(A_2061) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34136,plain,(
    ! [C_2062] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2062),'#skF_8')
      | ~ r2_hidden(C_2062,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32101,c_34114])).

tff(c_34145,plain,(
    ! [C_2062] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_2062),'#skF_8')
      | ~ r2_hidden(C_2062,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_34136])).

tff(c_34147,plain,(
    ! [C_2063] : ~ r2_hidden(C_2063,k2_relat_1('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_32100,c_34145])).

tff(c_34170,plain,(
    ! [B_2064] : r1_tarski(k2_relat_1('#skF_9'),B_2064) ),
    inference(resolution,[status(thm)],[c_20,c_34147])).

tff(c_33425,plain,(
    ! [C_2021,A_2022,B_2023] :
      ( m1_subset_1(C_2021,k1_zfmisc_1(k2_zfmisc_1(A_2022,B_2023)))
      | ~ r1_tarski(k2_relat_1(C_2021),B_2023)
      | ~ r1_tarski(k1_relat_1(C_2021),A_2022)
      | ~ v1_relat_1(C_2021) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_33460,plain,(
    ! [C_2021,B_1945] :
      ( m1_subset_1(C_2021,k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1(C_2021),'#skF_8')
      | ~ r1_tarski(k1_relat_1(C_2021),B_1945)
      | ~ v1_relat_1(C_2021) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32310,c_33425])).

tff(c_34177,plain,(
    ! [B_1945] :
      ( m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),B_1945)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34170,c_33460])).

tff(c_34207,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_32096,c_32101,c_34177])).

tff(c_34209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32326,c_34207])).

%------------------------------------------------------------------------------
