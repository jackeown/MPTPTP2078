%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 11.18s
% Output     : CNFRefutation 11.39s
% Verified   : 
% Statistics : Number of formulae       :  218 (3485 expanded)
%              Number of leaves         :   38 (1213 expanded)
%              Depth                    :   13
%              Number of atoms          :  394 (11218 expanded)
%              Number of equality atoms :  114 (4419 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
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

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_212,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_221,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_212])).

tff(c_62,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_222,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_62])).

tff(c_238,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k2_relset_1(A_118,B_119,C_120),k1_zfmisc_1(B_119))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_255,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_238])).

tff(c_261,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_255])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_269,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_261,c_14])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_276,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_269,c_8])).

tff(c_281,plain,(
    ~ r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_276])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_170,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_179,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_170])).

tff(c_16054,plain,(
    ! [B_1633,A_1634,C_1635] :
      ( k1_xboole_0 = B_1633
      | k1_relset_1(A_1634,B_1633,C_1635) = A_1634
      | ~ v1_funct_2(C_1635,A_1634,B_1633)
      | ~ m1_subset_1(C_1635,k1_zfmisc_1(k2_zfmisc_1(A_1634,B_1633))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16065,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_16054])).

tff(c_16070,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_179,c_16065])).

tff(c_16071,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16070])).

tff(c_72,plain,(
    ! [D_70] :
      ( r2_hidden('#skF_9'(D_70),'#skF_6')
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_145,plain,(
    ! [C_91,B_92,A_93] :
      ( r2_hidden(C_91,B_92)
      | ~ r2_hidden(C_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [D_70,B_92] :
      ( r2_hidden('#skF_9'(D_70),B_92)
      | ~ r1_tarski('#skF_6',B_92)
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_145])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_104])).

tff(c_114,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_110])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_70,plain,(
    ! [D_70] :
      ( k1_funct_1('#skF_8','#skF_9'(D_70)) = D_70
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8822,plain,(
    ! [A_993,D_994] :
      ( r2_hidden(k1_funct_1(A_993,D_994),k2_relat_1(A_993))
      | ~ r2_hidden(D_994,k1_relat_1(A_993))
      | ~ v1_funct_1(A_993)
      | ~ v1_relat_1(A_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8827,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_70),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8822])).

tff(c_10143,plain,(
    ! [D_1144] :
      ( r2_hidden(D_1144,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_1144),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_1144,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_68,c_8827])).

tff(c_10148,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_151,c_10143])).

tff(c_10174,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_10148])).

tff(c_16074,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16071,c_10174])).

tff(c_16079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16074])).

tff(c_16081,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16070])).

tff(c_94,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_94])).

tff(c_16080,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_16070])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10126,plain,(
    ! [C_1141,A_1142] :
      ( k1_xboole_0 = C_1141
      | ~ v1_funct_2(C_1141,A_1142,k1_xboole_0)
      | k1_xboole_0 = A_1142
      | ~ m1_subset_1(C_1141,k1_zfmisc_1(k2_zfmisc_1(A_1142,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10136,plain,(
    ! [A_8,A_1142] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_1142,k1_xboole_0)
      | k1_xboole_0 = A_1142
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_1142,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_10126])).

tff(c_19518,plain,(
    ! [A_1888,A_1889] :
      ( A_1888 = '#skF_7'
      | ~ v1_funct_2(A_1888,A_1889,'#skF_7')
      | A_1889 = '#skF_7'
      | ~ r1_tarski(A_1888,k2_zfmisc_1(A_1889,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16080,c_16080,c_16080,c_16080,c_10136])).

tff(c_19535,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_98,c_19518])).

tff(c_19546,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19535])).

tff(c_19548,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_19546])).

tff(c_19610,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19548,c_66])).

tff(c_19606,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19548,c_98])).

tff(c_10175,plain,(
    ! [B_1150,C_1151] :
      ( k1_relset_1(k1_xboole_0,B_1150,C_1151) = k1_xboole_0
      | ~ v1_funct_2(C_1151,k1_xboole_0,B_1150)
      | ~ m1_subset_1(C_1151,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_1150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10185,plain,(
    ! [B_1150,A_8] :
      ( k1_relset_1(k1_xboole_0,B_1150,A_8) = k1_xboole_0
      | ~ v1_funct_2(A_8,k1_xboole_0,B_1150)
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_1150)) ) ),
    inference(resolution,[status(thm)],[c_16,c_10175])).

tff(c_16084,plain,(
    ! [B_1150,A_8] :
      ( k1_relset_1('#skF_7',B_1150,A_8) = '#skF_7'
      | ~ v1_funct_2(A_8,'#skF_7',B_1150)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_7',B_1150)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16080,c_16080,c_16080,c_16080,c_10185])).

tff(c_19774,plain,(
    ! [B_1892,A_1893] :
      ( k1_relset_1('#skF_6',B_1892,A_1893) = '#skF_6'
      | ~ v1_funct_2(A_1893,'#skF_6',B_1892)
      | ~ r1_tarski(A_1893,k2_zfmisc_1('#skF_6',B_1892)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19548,c_19548,c_19548,c_19548,c_16084])).

tff(c_19777,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_19606,c_19774])).

tff(c_19792,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19610,c_19777])).

tff(c_19603,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19548,c_179])).

tff(c_19899,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19792,c_19603])).

tff(c_19900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16081,c_19899])).

tff(c_19901,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_19546])).

tff(c_152,plain,(
    ! [D_94,B_95] :
      ( r2_hidden('#skF_9'(D_94),B_95)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_145])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_196,plain,(
    ! [D_107,B_108,B_109] :
      ( r2_hidden('#skF_9'(D_107),B_108)
      | ~ r1_tarski(B_109,B_108)
      | ~ r1_tarski('#skF_6',B_109)
      | ~ r2_hidden(D_107,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_201,plain,(
    ! [D_107] :
      ( r2_hidden('#skF_9'(D_107),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski('#skF_6','#skF_8')
      | ~ r2_hidden(D_107,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_98,c_196])).

tff(c_282,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_5211,plain,(
    ! [B_740,A_741,C_742] :
      ( k1_xboole_0 = B_740
      | k1_relset_1(A_741,B_740,C_742) = A_741
      | ~ v1_funct_2(C_742,A_741,B_740)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_741,B_740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5222,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_5211])).

tff(c_5227,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_179,c_5222])).

tff(c_5228,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5227])).

tff(c_2173,plain,(
    ! [A_344,D_345] :
      ( r2_hidden(k1_funct_1(A_344,D_345),k2_relat_1(A_344))
      | ~ r2_hidden(D_345,k1_relat_1(A_344))
      | ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2178,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_70),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2173])).

tff(c_2239,plain,(
    ! [D_353] :
      ( r2_hidden(D_353,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_353),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_353,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_68,c_2178])).

tff(c_2244,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_151,c_2239])).

tff(c_2245,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2244])).

tff(c_5229,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5228,c_2245])).

tff(c_5234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_5229])).

tff(c_5235,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_5227])).

tff(c_4864,plain,(
    ! [C_695,A_696] :
      ( k1_xboole_0 = C_695
      | ~ v1_funct_2(C_695,A_696,k1_xboole_0)
      | k1_xboole_0 = A_696
      | ~ m1_subset_1(C_695,k1_zfmisc_1(k2_zfmisc_1(A_696,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4874,plain,(
    ! [A_8,A_696] :
      ( k1_xboole_0 = A_8
      | ~ v1_funct_2(A_8,A_696,k1_xboole_0)
      | k1_xboole_0 = A_696
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_696,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_4864])).

tff(c_8199,plain,(
    ! [A_957,A_958] :
      ( A_957 = '#skF_7'
      | ~ v1_funct_2(A_957,A_958,'#skF_7')
      | A_958 = '#skF_7'
      | ~ r1_tarski(A_957,k2_zfmisc_1(A_958,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_5235,c_5235,c_5235,c_4874])).

tff(c_8219,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_98,c_8199])).

tff(c_8236,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8219])).

tff(c_8238,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8236])).

tff(c_5236,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5227])).

tff(c_7129,plain,(
    ! [A_887,A_888] :
      ( A_887 = '#skF_7'
      | ~ v1_funct_2(A_887,A_888,'#skF_7')
      | A_888 = '#skF_7'
      | ~ r1_tarski(A_887,k2_zfmisc_1(A_888,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_5235,c_5235,c_5235,c_4874])).

tff(c_7143,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_98,c_7129])).

tff(c_7153,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_7143])).

tff(c_7155,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7153])).

tff(c_7206,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7155,c_66])).

tff(c_7199,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7155,c_179])).

tff(c_7202,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7155,c_98])).

tff(c_4920,plain,(
    ! [B_704,C_705] :
      ( k1_relset_1(k1_xboole_0,B_704,C_705) = k1_xboole_0
      | ~ v1_funct_2(C_705,k1_xboole_0,B_704)
      | ~ m1_subset_1(C_705,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_704))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4930,plain,(
    ! [B_704,A_8] :
      ( k1_relset_1(k1_xboole_0,B_704,A_8) = k1_xboole_0
      | ~ v1_funct_2(A_8,k1_xboole_0,B_704)
      | ~ r1_tarski(A_8,k2_zfmisc_1(k1_xboole_0,B_704)) ) ),
    inference(resolution,[status(thm)],[c_16,c_4920])).

tff(c_5242,plain,(
    ! [B_704,A_8] :
      ( k1_relset_1('#skF_7',B_704,A_8) = '#skF_7'
      | ~ v1_funct_2(A_8,'#skF_7',B_704)
      | ~ r1_tarski(A_8,k2_zfmisc_1('#skF_7',B_704)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_5235,c_5235,c_5235,c_4930])).

tff(c_7478,plain,(
    ! [B_908,A_909] :
      ( k1_relset_1('#skF_6',B_908,A_909) = '#skF_6'
      | ~ v1_funct_2(A_909,'#skF_6',B_908)
      | ~ r1_tarski(A_909,k2_zfmisc_1('#skF_6',B_908)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7155,c_7155,c_7155,c_7155,c_5242])).

tff(c_7484,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_7202,c_7478])).

tff(c_7500,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7206,c_7199,c_7484])).

tff(c_7502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5236,c_7500])).

tff(c_7503,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_7153])).

tff(c_156,plain,(
    ! [A_96,B_97,B_98] :
      ( r2_hidden('#skF_1'(A_96,B_97),B_98)
      | ~ r1_tarski(A_96,B_98)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_4960,plain,(
    ! [A_710,B_711,B_712,B_713] :
      ( r2_hidden('#skF_1'(A_710,B_711),B_712)
      | ~ r1_tarski(B_713,B_712)
      | ~ r1_tarski(A_710,B_713)
      | r1_tarski(A_710,B_711) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_5033,plain,(
    ! [A_721,B_722] :
      ( r2_hidden('#skF_1'(A_721,B_722),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski(A_721,'#skF_8')
      | r1_tarski(A_721,B_722) ) ),
    inference(resolution,[status(thm)],[c_98,c_4960])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5041,plain,(
    ! [A_721] :
      ( ~ r1_tarski(A_721,'#skF_8')
      | r1_tarski(A_721,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_5033,c_4])).

tff(c_165,plain,(
    ! [A_99] :
      ( v1_funct_2(k1_xboole_0,A_99,k1_xboole_0)
      | k1_xboole_0 = A_99
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_99,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_169,plain,(
    ! [A_99] :
      ( v1_funct_2(k1_xboole_0,A_99,k1_xboole_0)
      | k1_xboole_0 = A_99
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_99,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_165])).

tff(c_6977,plain,(
    ! [A_860] :
      ( v1_funct_2('#skF_7',A_860,'#skF_7')
      | A_860 = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_860,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_5235,c_5235,c_5235,c_5235,c_169])).

tff(c_6982,plain,
    ( v1_funct_2('#skF_7','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_5041,c_6977])).

tff(c_6983,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_6982])).

tff(c_7519,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7503,c_6983])).

tff(c_7558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_7519])).

tff(c_7560,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_6982])).

tff(c_155,plain,(
    ! [D_94,B_2,B_95] :
      ( r2_hidden('#skF_9'(D_94),B_2)
      | ~ r1_tarski(B_95,B_2)
      | ~ r1_tarski('#skF_6',B_95)
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_7586,plain,(
    ! [D_94] :
      ( r2_hidden('#skF_9'(D_94),'#skF_8')
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7560,c_155])).

tff(c_7609,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7586])).

tff(c_8273,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8238,c_7609])).

tff(c_8314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8273])).

tff(c_8315,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8236])).

tff(c_7590,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_7560,c_8])).

tff(c_7614,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7590])).

tff(c_8352,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8315,c_7614])).

tff(c_8399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8352])).

tff(c_8400,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_7590])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5256,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_5235,c_22])).

tff(c_8412,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8400,c_8400,c_5256])).

tff(c_8431,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8400,c_222])).

tff(c_8492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8412,c_8431])).

tff(c_8494,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_7586])).

tff(c_163,plain,(
    ! [A_96,B_97,B_2,B_98] :
      ( r2_hidden('#skF_1'(A_96,B_97),B_2)
      | ~ r1_tarski(B_98,B_2)
      | ~ r1_tarski(A_96,B_98)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_8716,plain,(
    ! [A_982,B_983] :
      ( r2_hidden('#skF_1'(A_982,B_983),'#skF_8')
      | ~ r1_tarski(A_982,'#skF_7')
      | r1_tarski(A_982,B_983) ) ),
    inference(resolution,[status(thm)],[c_7560,c_163])).

tff(c_8725,plain,(
    ! [A_984] :
      ( ~ r1_tarski(A_984,'#skF_7')
      | r1_tarski(A_984,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8716,c_4])).

tff(c_8728,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_8494,c_8725])).

tff(c_8750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_8728])).

tff(c_8777,plain,(
    ! [D_987] :
      ( r2_hidden(D_987,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_987,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_2244])).

tff(c_8792,plain,(
    ! [A_992] :
      ( r1_tarski(A_992,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_992,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8777,c_4])).

tff(c_8800,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_8792])).

tff(c_8805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_281,c_8800])).

tff(c_8807,plain,(
    r1_tarski('#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_19078,plain,(
    ! [A_1861,A_1862] :
      ( A_1861 = '#skF_7'
      | ~ v1_funct_2(A_1861,A_1862,'#skF_7')
      | A_1862 = '#skF_7'
      | ~ r1_tarski(A_1861,k2_zfmisc_1(A_1862,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16080,c_16080,c_16080,c_16080,c_10136])).

tff(c_19095,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_98,c_19078])).

tff(c_19106,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19095])).

tff(c_19108,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_19106])).

tff(c_15939,plain,(
    ! [A_1622,B_1623,B_1624,B_1625] :
      ( r2_hidden('#skF_1'(A_1622,B_1623),B_1624)
      | ~ r1_tarski(B_1625,B_1624)
      | ~ r1_tarski(A_1622,B_1625)
      | r1_tarski(A_1622,B_1623) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_15958,plain,(
    ! [A_1626,B_1627] :
      ( r2_hidden('#skF_1'(A_1626,B_1627),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r1_tarski(A_1626,'#skF_8')
      | r1_tarski(A_1626,B_1627) ) ),
    inference(resolution,[status(thm)],[c_98,c_15939])).

tff(c_15966,plain,(
    ! [A_1626] :
      ( ~ r1_tarski(A_1626,'#skF_8')
      | r1_tarski(A_1626,k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_15958,c_4])).

tff(c_18896,plain,(
    ! [A_1831] :
      ( v1_funct_2('#skF_7',A_1831,'#skF_7')
      | A_1831 = '#skF_7'
      | ~ r1_tarski('#skF_7',k2_zfmisc_1(A_1831,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16080,c_16080,c_16080,c_16080,c_16080,c_169])).

tff(c_18901,plain,
    ( v1_funct_2('#skF_7','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_15966,c_18896])).

tff(c_18902,plain,(
    ~ r1_tarski('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_18901])).

tff(c_19122,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19108,c_18902])).

tff(c_19172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8807,c_19122])).

tff(c_19173,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_19106])).

tff(c_19203,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19173,c_18902])).

tff(c_19253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19203])).

tff(c_19255,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_18901])).

tff(c_19288,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_19255,c_8])).

tff(c_19312,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_19288])).

tff(c_19929,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19901,c_19312])).

tff(c_19982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19929])).

tff(c_19983,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_19288])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16103,plain,(
    k1_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16080,c_16080,c_24])).

tff(c_20001,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19983,c_19983,c_16103])).

tff(c_8809,plain,(
    ! [D_94] :
      ( r2_hidden('#skF_9'(D_94),'#skF_8')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_94,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8807,c_155])).

tff(c_10139,plain,(
    ! [D_1143] :
      ( r2_hidden('#skF_9'(D_1143),'#skF_8')
      | ~ r2_hidden(D_1143,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8809])).

tff(c_10165,plain,(
    ! [D_1148,B_1149] :
      ( r2_hidden('#skF_9'(D_1148),B_1149)
      | ~ r1_tarski('#skF_8',B_1149)
      | ~ r2_hidden(D_1148,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10139,c_2])).

tff(c_8833,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_70),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_70,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_68,c_8827])).

tff(c_10172,plain,(
    ! [D_1148] :
      ( r2_hidden(D_1148,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_8',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_1148,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10165,c_8833])).

tff(c_10187,plain,(
    ~ r1_tarski('#skF_8',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_10172])).

tff(c_20047,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20001,c_10187])).

tff(c_20051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20047])).

tff(c_20078,plain,(
    ! [D_1900] :
      ( r2_hidden(D_1900,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1900,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_10172])).

tff(c_20092,plain,(
    ! [A_1902] :
      ( r1_tarski(A_1902,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_1902,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20078,c_4])).

tff(c_20100,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_20092])).

tff(c_20105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_281,c_20100])).

tff(c_20121,plain,(
    ! [D_1903] :
      ( r2_hidden(D_1903,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1903,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_10148])).

tff(c_20146,plain,(
    ! [A_1907] :
      ( r1_tarski(A_1907,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_1907,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20121,c_4])).

tff(c_20154,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_20146])).

tff(c_20159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_281,c_20154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.28  % Computer   : n011.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 19:59:26 EST 2020
% 0.08/0.29  % CPUTime    : 
% 0.08/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.18/4.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.18/4.11  
% 11.18/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.18/4.11  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.18/4.11  
% 11.18/4.11  %Foreground sorts:
% 11.18/4.11  
% 11.18/4.11  
% 11.18/4.11  %Background operators:
% 11.18/4.11  
% 11.18/4.11  
% 11.18/4.11  %Foreground operators:
% 11.18/4.11  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.18/4.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.18/4.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.18/4.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.18/4.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.18/4.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.18/4.11  tff('#skF_7', type, '#skF_7': $i).
% 11.18/4.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.18/4.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.18/4.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.18/4.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.18/4.11  tff('#skF_6', type, '#skF_6': $i).
% 11.18/4.11  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.18/4.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.18/4.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.18/4.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.18/4.11  tff('#skF_8', type, '#skF_8': $i).
% 11.18/4.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.18/4.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.18/4.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.18/4.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.18/4.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.18/4.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.18/4.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.18/4.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.18/4.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.18/4.11  
% 11.39/4.13  tff(f_118, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 11.39/4.13  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.39/4.13  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 11.39/4.13  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.39/4.13  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.39/4.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.39/4.13  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.39/4.13  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.39/4.13  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.39/4.13  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.39/4.13  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 11.39/4.13  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 11.39/4.13  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.39/4.13  tff(c_212, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.13  tff(c_221, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_212])).
% 11.39/4.13  tff(c_62, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.39/4.13  tff(c_222, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_62])).
% 11.39/4.13  tff(c_238, plain, (![A_118, B_119, C_120]: (m1_subset_1(k2_relset_1(A_118, B_119, C_120), k1_zfmisc_1(B_119)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.39/4.13  tff(c_255, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_221, c_238])).
% 11.39/4.13  tff(c_261, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_255])).
% 11.39/4.13  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.39/4.13  tff(c_269, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_261, c_14])).
% 11.39/4.13  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.39/4.13  tff(c_276, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_269, c_8])).
% 11.39/4.13  tff(c_281, plain, (~r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_222, c_276])).
% 11.39/4.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.39/4.13  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.39/4.13  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.39/4.13  tff(c_170, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.39/4.13  tff(c_179, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_170])).
% 11.39/4.13  tff(c_16054, plain, (![B_1633, A_1634, C_1635]: (k1_xboole_0=B_1633 | k1_relset_1(A_1634, B_1633, C_1635)=A_1634 | ~v1_funct_2(C_1635, A_1634, B_1633) | ~m1_subset_1(C_1635, k1_zfmisc_1(k2_zfmisc_1(A_1634, B_1633))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.13  tff(c_16065, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_16054])).
% 11.39/4.13  tff(c_16070, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_179, c_16065])).
% 11.39/4.13  tff(c_16071, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_16070])).
% 11.39/4.13  tff(c_72, plain, (![D_70]: (r2_hidden('#skF_9'(D_70), '#skF_6') | ~r2_hidden(D_70, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.39/4.13  tff(c_145, plain, (![C_91, B_92, A_93]: (r2_hidden(C_91, B_92) | ~r2_hidden(C_91, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.39/4.13  tff(c_151, plain, (![D_70, B_92]: (r2_hidden('#skF_9'(D_70), B_92) | ~r1_tarski('#skF_6', B_92) | ~r2_hidden(D_70, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_145])).
% 11.39/4.13  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.39/4.13  tff(c_104, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.39/4.13  tff(c_110, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_104])).
% 11.39/4.13  tff(c_114, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_110])).
% 11.39/4.13  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.39/4.13  tff(c_70, plain, (![D_70]: (k1_funct_1('#skF_8', '#skF_9'(D_70))=D_70 | ~r2_hidden(D_70, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.39/4.13  tff(c_8822, plain, (![A_993, D_994]: (r2_hidden(k1_funct_1(A_993, D_994), k2_relat_1(A_993)) | ~r2_hidden(D_994, k1_relat_1(A_993)) | ~v1_funct_1(A_993) | ~v1_relat_1(A_993))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.39/4.13  tff(c_8827, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_70), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_70, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8822])).
% 11.39/4.13  tff(c_10143, plain, (![D_1144]: (r2_hidden(D_1144, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_1144), k1_relat_1('#skF_8')) | ~r2_hidden(D_1144, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_68, c_8827])).
% 11.39/4.13  tff(c_10148, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_70, '#skF_7'))), inference(resolution, [status(thm)], [c_151, c_10143])).
% 11.39/4.13  tff(c_10174, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_10148])).
% 11.39/4.13  tff(c_16074, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16071, c_10174])).
% 11.39/4.13  tff(c_16079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_16074])).
% 11.39/4.13  tff(c_16081, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_16070])).
% 11.39/4.13  tff(c_94, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.39/4.13  tff(c_98, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_94])).
% 11.39/4.13  tff(c_16080, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_16070])).
% 11.39/4.13  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.39/4.13  tff(c_10126, plain, (![C_1141, A_1142]: (k1_xboole_0=C_1141 | ~v1_funct_2(C_1141, A_1142, k1_xboole_0) | k1_xboole_0=A_1142 | ~m1_subset_1(C_1141, k1_zfmisc_1(k2_zfmisc_1(A_1142, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.13  tff(c_10136, plain, (![A_8, A_1142]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_1142, k1_xboole_0) | k1_xboole_0=A_1142 | ~r1_tarski(A_8, k2_zfmisc_1(A_1142, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_10126])).
% 11.39/4.13  tff(c_19518, plain, (![A_1888, A_1889]: (A_1888='#skF_7' | ~v1_funct_2(A_1888, A_1889, '#skF_7') | A_1889='#skF_7' | ~r1_tarski(A_1888, k2_zfmisc_1(A_1889, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_16080, c_16080, c_16080, c_16080, c_10136])).
% 11.39/4.13  tff(c_19535, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_98, c_19518])).
% 11.39/4.13  tff(c_19546, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_19535])).
% 11.39/4.13  tff(c_19548, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_19546])).
% 11.39/4.13  tff(c_19610, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19548, c_66])).
% 11.39/4.13  tff(c_19606, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_19548, c_98])).
% 11.39/4.13  tff(c_10175, plain, (![B_1150, C_1151]: (k1_relset_1(k1_xboole_0, B_1150, C_1151)=k1_xboole_0 | ~v1_funct_2(C_1151, k1_xboole_0, B_1150) | ~m1_subset_1(C_1151, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_1150))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.13  tff(c_10185, plain, (![B_1150, A_8]: (k1_relset_1(k1_xboole_0, B_1150, A_8)=k1_xboole_0 | ~v1_funct_2(A_8, k1_xboole_0, B_1150) | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_1150)))), inference(resolution, [status(thm)], [c_16, c_10175])).
% 11.39/4.13  tff(c_16084, plain, (![B_1150, A_8]: (k1_relset_1('#skF_7', B_1150, A_8)='#skF_7' | ~v1_funct_2(A_8, '#skF_7', B_1150) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_7', B_1150)))), inference(demodulation, [status(thm), theory('equality')], [c_16080, c_16080, c_16080, c_16080, c_10185])).
% 11.39/4.13  tff(c_19774, plain, (![B_1892, A_1893]: (k1_relset_1('#skF_6', B_1892, A_1893)='#skF_6' | ~v1_funct_2(A_1893, '#skF_6', B_1892) | ~r1_tarski(A_1893, k2_zfmisc_1('#skF_6', B_1892)))), inference(demodulation, [status(thm), theory('equality')], [c_19548, c_19548, c_19548, c_19548, c_16084])).
% 11.39/4.13  tff(c_19777, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_19606, c_19774])).
% 11.39/4.13  tff(c_19792, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19610, c_19777])).
% 11.39/4.13  tff(c_19603, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19548, c_179])).
% 11.39/4.13  tff(c_19899, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19792, c_19603])).
% 11.39/4.13  tff(c_19900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16081, c_19899])).
% 11.39/4.13  tff(c_19901, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_19546])).
% 11.39/4.13  tff(c_152, plain, (![D_94, B_95]: (r2_hidden('#skF_9'(D_94), B_95) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_145])).
% 11.39/4.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.39/4.13  tff(c_196, plain, (![D_107, B_108, B_109]: (r2_hidden('#skF_9'(D_107), B_108) | ~r1_tarski(B_109, B_108) | ~r1_tarski('#skF_6', B_109) | ~r2_hidden(D_107, '#skF_7'))), inference(resolution, [status(thm)], [c_152, c_2])).
% 11.39/4.13  tff(c_201, plain, (![D_107]: (r2_hidden('#skF_9'(D_107), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski('#skF_6', '#skF_8') | ~r2_hidden(D_107, '#skF_7'))), inference(resolution, [status(thm)], [c_98, c_196])).
% 11.39/4.13  tff(c_282, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_201])).
% 11.39/4.13  tff(c_5211, plain, (![B_740, A_741, C_742]: (k1_xboole_0=B_740 | k1_relset_1(A_741, B_740, C_742)=A_741 | ~v1_funct_2(C_742, A_741, B_740) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_741, B_740))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.13  tff(c_5222, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_5211])).
% 11.39/4.13  tff(c_5227, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_179, c_5222])).
% 11.39/4.13  tff(c_5228, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_5227])).
% 11.39/4.13  tff(c_2173, plain, (![A_344, D_345]: (r2_hidden(k1_funct_1(A_344, D_345), k2_relat_1(A_344)) | ~r2_hidden(D_345, k1_relat_1(A_344)) | ~v1_funct_1(A_344) | ~v1_relat_1(A_344))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.39/4.13  tff(c_2178, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_70), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_70, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2173])).
% 11.39/4.13  tff(c_2239, plain, (![D_353]: (r2_hidden(D_353, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_353), k1_relat_1('#skF_8')) | ~r2_hidden(D_353, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_68, c_2178])).
% 11.39/4.13  tff(c_2244, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_70, '#skF_7'))), inference(resolution, [status(thm)], [c_151, c_2239])).
% 11.39/4.13  tff(c_2245, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_2244])).
% 11.39/4.13  tff(c_5229, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5228, c_2245])).
% 11.39/4.13  tff(c_5234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_5229])).
% 11.39/4.13  tff(c_5235, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_5227])).
% 11.39/4.13  tff(c_4864, plain, (![C_695, A_696]: (k1_xboole_0=C_695 | ~v1_funct_2(C_695, A_696, k1_xboole_0) | k1_xboole_0=A_696 | ~m1_subset_1(C_695, k1_zfmisc_1(k2_zfmisc_1(A_696, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.13  tff(c_4874, plain, (![A_8, A_696]: (k1_xboole_0=A_8 | ~v1_funct_2(A_8, A_696, k1_xboole_0) | k1_xboole_0=A_696 | ~r1_tarski(A_8, k2_zfmisc_1(A_696, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_4864])).
% 11.39/4.13  tff(c_8199, plain, (![A_957, A_958]: (A_957='#skF_7' | ~v1_funct_2(A_957, A_958, '#skF_7') | A_958='#skF_7' | ~r1_tarski(A_957, k2_zfmisc_1(A_958, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_5235, c_5235, c_5235, c_4874])).
% 11.39/4.13  tff(c_8219, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_98, c_8199])).
% 11.39/4.13  tff(c_8236, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8219])).
% 11.39/4.13  tff(c_8238, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_8236])).
% 11.39/4.13  tff(c_5236, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_5227])).
% 11.39/4.13  tff(c_7129, plain, (![A_887, A_888]: (A_887='#skF_7' | ~v1_funct_2(A_887, A_888, '#skF_7') | A_888='#skF_7' | ~r1_tarski(A_887, k2_zfmisc_1(A_888, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_5235, c_5235, c_5235, c_4874])).
% 11.39/4.13  tff(c_7143, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_98, c_7129])).
% 11.39/4.13  tff(c_7153, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_7143])).
% 11.39/4.13  tff(c_7155, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_7153])).
% 11.39/4.13  tff(c_7206, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7155, c_66])).
% 11.39/4.13  tff(c_7199, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7155, c_179])).
% 11.39/4.13  tff(c_7202, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7155, c_98])).
% 11.39/4.13  tff(c_4920, plain, (![B_704, C_705]: (k1_relset_1(k1_xboole_0, B_704, C_705)=k1_xboole_0 | ~v1_funct_2(C_705, k1_xboole_0, B_704) | ~m1_subset_1(C_705, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_704))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.13  tff(c_4930, plain, (![B_704, A_8]: (k1_relset_1(k1_xboole_0, B_704, A_8)=k1_xboole_0 | ~v1_funct_2(A_8, k1_xboole_0, B_704) | ~r1_tarski(A_8, k2_zfmisc_1(k1_xboole_0, B_704)))), inference(resolution, [status(thm)], [c_16, c_4920])).
% 11.39/4.13  tff(c_5242, plain, (![B_704, A_8]: (k1_relset_1('#skF_7', B_704, A_8)='#skF_7' | ~v1_funct_2(A_8, '#skF_7', B_704) | ~r1_tarski(A_8, k2_zfmisc_1('#skF_7', B_704)))), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_5235, c_5235, c_5235, c_4930])).
% 11.39/4.13  tff(c_7478, plain, (![B_908, A_909]: (k1_relset_1('#skF_6', B_908, A_909)='#skF_6' | ~v1_funct_2(A_909, '#skF_6', B_908) | ~r1_tarski(A_909, k2_zfmisc_1('#skF_6', B_908)))), inference(demodulation, [status(thm), theory('equality')], [c_7155, c_7155, c_7155, c_7155, c_5242])).
% 11.39/4.13  tff(c_7484, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_7202, c_7478])).
% 11.39/4.13  tff(c_7500, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7206, c_7199, c_7484])).
% 11.39/4.13  tff(c_7502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5236, c_7500])).
% 11.39/4.13  tff(c_7503, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_7153])).
% 11.39/4.13  tff(c_156, plain, (![A_96, B_97, B_98]: (r2_hidden('#skF_1'(A_96, B_97), B_98) | ~r1_tarski(A_96, B_98) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_6, c_145])).
% 11.39/4.14  tff(c_4960, plain, (![A_710, B_711, B_712, B_713]: (r2_hidden('#skF_1'(A_710, B_711), B_712) | ~r1_tarski(B_713, B_712) | ~r1_tarski(A_710, B_713) | r1_tarski(A_710, B_711))), inference(resolution, [status(thm)], [c_156, c_2])).
% 11.39/4.14  tff(c_5033, plain, (![A_721, B_722]: (r2_hidden('#skF_1'(A_721, B_722), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski(A_721, '#skF_8') | r1_tarski(A_721, B_722))), inference(resolution, [status(thm)], [c_98, c_4960])).
% 11.39/4.14  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.39/4.14  tff(c_5041, plain, (![A_721]: (~r1_tarski(A_721, '#skF_8') | r1_tarski(A_721, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_5033, c_4])).
% 11.39/4.14  tff(c_165, plain, (![A_99]: (v1_funct_2(k1_xboole_0, A_99, k1_xboole_0) | k1_xboole_0=A_99 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_99, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.39/4.14  tff(c_169, plain, (![A_99]: (v1_funct_2(k1_xboole_0, A_99, k1_xboole_0) | k1_xboole_0=A_99 | ~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_99, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_165])).
% 11.39/4.14  tff(c_6977, plain, (![A_860]: (v1_funct_2('#skF_7', A_860, '#skF_7') | A_860='#skF_7' | ~r1_tarski('#skF_7', k2_zfmisc_1(A_860, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_5235, c_5235, c_5235, c_5235, c_169])).
% 11.39/4.14  tff(c_6982, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_5041, c_6977])).
% 11.39/4.14  tff(c_6983, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_6982])).
% 11.39/4.14  tff(c_7519, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7503, c_6983])).
% 11.39/4.14  tff(c_7558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_7519])).
% 11.39/4.14  tff(c_7560, plain, (r1_tarski('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_6982])).
% 11.39/4.14  tff(c_155, plain, (![D_94, B_2, B_95]: (r2_hidden('#skF_9'(D_94), B_2) | ~r1_tarski(B_95, B_2) | ~r1_tarski('#skF_6', B_95) | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_152, c_2])).
% 11.39/4.14  tff(c_7586, plain, (![D_94]: (r2_hidden('#skF_9'(D_94), '#skF_8') | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_7560, c_155])).
% 11.39/4.14  tff(c_7609, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_7586])).
% 11.39/4.14  tff(c_8273, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8238, c_7609])).
% 11.39/4.14  tff(c_8314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8273])).
% 11.39/4.14  tff(c_8315, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_8236])).
% 11.39/4.14  tff(c_7590, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_7560, c_8])).
% 11.39/4.14  tff(c_7614, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_7590])).
% 11.39/4.14  tff(c_8352, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8315, c_7614])).
% 11.39/4.14  tff(c_8399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_8352])).
% 11.39/4.14  tff(c_8400, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_7590])).
% 11.39/4.14  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.39/4.14  tff(c_5256, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_5235, c_22])).
% 11.39/4.14  tff(c_8412, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8400, c_8400, c_5256])).
% 11.39/4.14  tff(c_8431, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_8400, c_222])).
% 11.39/4.14  tff(c_8492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8412, c_8431])).
% 11.39/4.14  tff(c_8494, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_7586])).
% 11.39/4.14  tff(c_163, plain, (![A_96, B_97, B_2, B_98]: (r2_hidden('#skF_1'(A_96, B_97), B_2) | ~r1_tarski(B_98, B_2) | ~r1_tarski(A_96, B_98) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_156, c_2])).
% 11.39/4.14  tff(c_8716, plain, (![A_982, B_983]: (r2_hidden('#skF_1'(A_982, B_983), '#skF_8') | ~r1_tarski(A_982, '#skF_7') | r1_tarski(A_982, B_983))), inference(resolution, [status(thm)], [c_7560, c_163])).
% 11.39/4.14  tff(c_8725, plain, (![A_984]: (~r1_tarski(A_984, '#skF_7') | r1_tarski(A_984, '#skF_8'))), inference(resolution, [status(thm)], [c_8716, c_4])).
% 11.39/4.14  tff(c_8728, plain, (r1_tarski('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_8494, c_8725])).
% 11.39/4.14  tff(c_8750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_8728])).
% 11.39/4.14  tff(c_8777, plain, (![D_987]: (r2_hidden(D_987, k2_relat_1('#skF_8')) | ~r2_hidden(D_987, '#skF_7'))), inference(splitRight, [status(thm)], [c_2244])).
% 11.39/4.14  tff(c_8792, plain, (![A_992]: (r1_tarski(A_992, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_992, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_8777, c_4])).
% 11.39/4.14  tff(c_8800, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_8792])).
% 11.39/4.14  tff(c_8805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_281, c_8800])).
% 11.39/4.14  tff(c_8807, plain, (r1_tarski('#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_201])).
% 11.39/4.14  tff(c_19078, plain, (![A_1861, A_1862]: (A_1861='#skF_7' | ~v1_funct_2(A_1861, A_1862, '#skF_7') | A_1862='#skF_7' | ~r1_tarski(A_1861, k2_zfmisc_1(A_1862, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_16080, c_16080, c_16080, c_16080, c_10136])).
% 11.39/4.14  tff(c_19095, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_98, c_19078])).
% 11.39/4.14  tff(c_19106, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_19095])).
% 11.39/4.14  tff(c_19108, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_19106])).
% 11.39/4.14  tff(c_15939, plain, (![A_1622, B_1623, B_1624, B_1625]: (r2_hidden('#skF_1'(A_1622, B_1623), B_1624) | ~r1_tarski(B_1625, B_1624) | ~r1_tarski(A_1622, B_1625) | r1_tarski(A_1622, B_1623))), inference(resolution, [status(thm)], [c_156, c_2])).
% 11.39/4.14  tff(c_15958, plain, (![A_1626, B_1627]: (r2_hidden('#skF_1'(A_1626, B_1627), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r1_tarski(A_1626, '#skF_8') | r1_tarski(A_1626, B_1627))), inference(resolution, [status(thm)], [c_98, c_15939])).
% 11.39/4.14  tff(c_15966, plain, (![A_1626]: (~r1_tarski(A_1626, '#skF_8') | r1_tarski(A_1626, k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_15958, c_4])).
% 11.39/4.14  tff(c_18896, plain, (![A_1831]: (v1_funct_2('#skF_7', A_1831, '#skF_7') | A_1831='#skF_7' | ~r1_tarski('#skF_7', k2_zfmisc_1(A_1831, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_16080, c_16080, c_16080, c_16080, c_16080, c_169])).
% 11.39/4.14  tff(c_18901, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_15966, c_18896])).
% 11.39/4.14  tff(c_18902, plain, (~r1_tarski('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_18901])).
% 11.39/4.14  tff(c_19122, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19108, c_18902])).
% 11.39/4.14  tff(c_19172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8807, c_19122])).
% 11.39/4.14  tff(c_19173, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_19106])).
% 11.39/4.14  tff(c_19203, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19173, c_18902])).
% 11.39/4.14  tff(c_19253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_19203])).
% 11.39/4.14  tff(c_19255, plain, (r1_tarski('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_18901])).
% 11.39/4.14  tff(c_19288, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_19255, c_8])).
% 11.39/4.14  tff(c_19312, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_19288])).
% 11.39/4.14  tff(c_19929, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19901, c_19312])).
% 11.39/4.14  tff(c_19982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_19929])).
% 11.39/4.14  tff(c_19983, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_19288])).
% 11.39/4.14  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.39/4.14  tff(c_16103, plain, (k1_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16080, c_16080, c_24])).
% 11.39/4.14  tff(c_20001, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_19983, c_19983, c_16103])).
% 11.39/4.14  tff(c_8809, plain, (![D_94]: (r2_hidden('#skF_9'(D_94), '#skF_8') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_94, '#skF_7'))), inference(resolution, [status(thm)], [c_8807, c_155])).
% 11.39/4.14  tff(c_10139, plain, (![D_1143]: (r2_hidden('#skF_9'(D_1143), '#skF_8') | ~r2_hidden(D_1143, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8809])).
% 11.39/4.14  tff(c_10165, plain, (![D_1148, B_1149]: (r2_hidden('#skF_9'(D_1148), B_1149) | ~r1_tarski('#skF_8', B_1149) | ~r2_hidden(D_1148, '#skF_7'))), inference(resolution, [status(thm)], [c_10139, c_2])).
% 11.39/4.14  tff(c_8833, plain, (![D_70]: (r2_hidden(D_70, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_70), k1_relat_1('#skF_8')) | ~r2_hidden(D_70, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_68, c_8827])).
% 11.39/4.14  tff(c_10172, plain, (![D_1148]: (r2_hidden(D_1148, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_8', k1_relat_1('#skF_8')) | ~r2_hidden(D_1148, '#skF_7'))), inference(resolution, [status(thm)], [c_10165, c_8833])).
% 11.39/4.14  tff(c_10187, plain, (~r1_tarski('#skF_8', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_10172])).
% 11.39/4.14  tff(c_20047, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20001, c_10187])).
% 11.39/4.14  tff(c_20051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_20047])).
% 11.39/4.14  tff(c_20078, plain, (![D_1900]: (r2_hidden(D_1900, k2_relat_1('#skF_8')) | ~r2_hidden(D_1900, '#skF_7'))), inference(splitRight, [status(thm)], [c_10172])).
% 11.39/4.14  tff(c_20092, plain, (![A_1902]: (r1_tarski(A_1902, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_1902, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_20078, c_4])).
% 11.39/4.14  tff(c_20100, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_20092])).
% 11.39/4.14  tff(c_20105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_281, c_20100])).
% 11.39/4.14  tff(c_20121, plain, (![D_1903]: (r2_hidden(D_1903, k2_relat_1('#skF_8')) | ~r2_hidden(D_1903, '#skF_7'))), inference(splitRight, [status(thm)], [c_10148])).
% 11.39/4.14  tff(c_20146, plain, (![A_1907]: (r1_tarski(A_1907, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_1907, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_20121, c_4])).
% 11.39/4.14  tff(c_20154, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_20146])).
% 11.39/4.14  tff(c_20159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_281, c_20154])).
% 11.39/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.14  
% 11.39/4.14  Inference rules
% 11.39/4.14  ----------------------
% 11.39/4.14  #Ref     : 29
% 11.39/4.14  #Sup     : 3661
% 11.39/4.14  #Fact    : 0
% 11.39/4.14  #Define  : 0
% 11.39/4.14  #Split   : 185
% 11.39/4.14  #Chain   : 0
% 11.39/4.14  #Close   : 0
% 11.39/4.14  
% 11.39/4.14  Ordering : KBO
% 11.39/4.14  
% 11.39/4.14  Simplification rules
% 11.39/4.14  ----------------------
% 11.39/4.14  #Subsume      : 735
% 11.39/4.14  #Demod        : 6895
% 11.39/4.14  #Tautology    : 1194
% 11.39/4.14  #SimpNegUnit  : 30
% 11.39/4.14  #BackRed      : 3004
% 11.39/4.14  
% 11.39/4.14  #Partial instantiations: 0
% 11.39/4.14  #Strategies tried      : 1
% 11.39/4.14  
% 11.39/4.14  Timing (in seconds)
% 11.39/4.14  ----------------------
% 11.39/4.14  Preprocessing        : 0.36
% 11.39/4.14  Parsing              : 0.18
% 11.39/4.14  CNF conversion       : 0.03
% 11.39/4.14  Main loop            : 3.08
% 11.39/4.14  Inferencing          : 0.94
% 11.39/4.14  Reduction            : 1.09
% 11.39/4.14  Demodulation         : 0.73
% 11.39/4.14  BG Simplification    : 0.11
% 11.39/4.14  Subsumption          : 0.68
% 11.39/4.14  Abstraction          : 0.12
% 11.39/4.14  MUC search           : 0.00
% 11.39/4.14  Cooper               : 0.00
% 11.39/4.14  Total                : 3.50
% 11.39/4.14  Index Insertion      : 0.00
% 11.39/4.14  Index Deletion       : 0.00
% 11.39/4.14  Index Matching       : 0.00
% 11.39/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
