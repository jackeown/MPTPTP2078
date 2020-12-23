%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:20 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 662 expanded)
%              Number of leaves         :   34 ( 234 expanded)
%              Depth                    :   13
%              Number of atoms          :  238 (2038 expanded)
%              Number of equality atoms :   74 ( 503 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1612,plain,(
    ! [A_181,B_182,D_183] :
      ( r2_relset_1(A_181,B_182,D_183,D_183)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1623,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_1612])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_241,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_223])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_128,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_144,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_128])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_480,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_505,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_480])).

tff(c_731,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_742,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_731])).

tff(c_758,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_505,c_742])).

tff(c_763,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_758])).

tff(c_145,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_128])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_506,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_480])).

tff(c_745,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_731])).

tff(c_761,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_506,c_745])).

tff(c_769,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_761])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,(
    ! [E_50] :
      ( k1_funct_1('#skF_5',E_50) = k1_funct_1('#skF_6',E_50)
      | ~ m1_subset_1(E_50,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_127,plain,(
    ! [B_10] :
      ( k1_funct_1('#skF_5',B_10) = k1_funct_1('#skF_6',B_10)
      | ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_122])).

tff(c_169,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_944,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_2'(A_140,B_141),k1_relat_1(A_140))
      | B_141 = A_140
      | k1_relat_1(B_141) != k1_relat_1(A_140)
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_953,plain,(
    ! [B_141] :
      ( r2_hidden('#skF_2'('#skF_6',B_141),'#skF_3')
      | B_141 = '#skF_6'
      | k1_relat_1(B_141) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_944])).

tff(c_998,plain,(
    ! [B_148] :
      ( r2_hidden('#skF_2'('#skF_6',B_148),'#skF_3')
      | B_148 = '#skF_6'
      | k1_relat_1(B_148) != '#skF_3'
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_58,c_769,c_953])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ r2_hidden(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1001,plain,(
    ! [B_148] :
      ( m1_subset_1('#skF_2'('#skF_6',B_148),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_148 = '#skF_6'
      | k1_relat_1(B_148) != '#skF_3'
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_998,c_16])).

tff(c_1142,plain,(
    ! [B_156] :
      ( m1_subset_1('#skF_2'('#skF_6',B_156),'#skF_3')
      | B_156 = '#skF_6'
      | k1_relat_1(B_156) != '#skF_3'
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_1001])).

tff(c_52,plain,(
    ! [E_37] :
      ( k1_funct_1('#skF_5',E_37) = k1_funct_1('#skF_6',E_37)
      | ~ m1_subset_1(E_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1151,plain,(
    ! [B_157] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_157)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_157))
      | B_157 = '#skF_6'
      | k1_relat_1(B_157) != '#skF_3'
      | ~ v1_funct_1(B_157)
      | ~ v1_relat_1(B_157) ) ),
    inference(resolution,[status(thm)],[c_1142,c_52])).

tff(c_26,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_2'(A_14,B_18)) != k1_funct_1(A_14,'#skF_2'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1158,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_26])).

tff(c_1165,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_64,c_763,c_145,c_58,c_769,c_763,c_1158])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1176,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1165,c_50])).

tff(c_1186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_1176])).

tff(c_1187,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_761])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1216,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_6])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1215,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_1187,c_12])).

tff(c_207,plain,(
    ! [C_62,B_63,A_64] :
      ( ~ v1_xboole_0(C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_220,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_64,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_207])).

tff(c_222,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_1243,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_222])).

tff(c_1248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1243])).

tff(c_1249,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_758])).

tff(c_1278,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_6])).

tff(c_1277,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1249,c_12])).

tff(c_1302,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_222])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1302])).

tff(c_1309,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_221,plain,(
    ! [A_64] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_64,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_207])).

tff(c_1542,plain,(
    ! [A_178] : ~ r2_hidden(A_178,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_221])).

tff(c_1552,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_1542])).

tff(c_1310,plain,(
    ! [A_164] : ~ r2_hidden(A_164,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_1320,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1310])).

tff(c_92,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | B_42 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_92])).

tff(c_1326,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1320,c_95])).

tff(c_1575,plain,(
    ! [A_180] :
      ( A_180 = '#skF_5'
      | ~ v1_xboole_0(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_95])).

tff(c_1585,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1552,c_1575])).

tff(c_1600,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_50])).

tff(c_1715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1600])).

tff(c_1717,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_1723,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1717,c_95])).

tff(c_38,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_67,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_1922,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_3',A_30,'#skF_3')
      | A_30 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_1723,c_1723,c_1723,c_1723,c_67])).

tff(c_1923,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1922])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1729,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_3',B_8) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_1723,c_14])).

tff(c_1763,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_54])).

tff(c_1828,plain,(
    ! [C_197,B_198,A_199] :
      ( ~ v1_xboole_0(C_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(C_197))
      | ~ r2_hidden(A_199,B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1833,plain,(
    ! [A_199] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_199,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1763,c_1828])).

tff(c_1847,plain,(
    ! [A_200] : ~ r2_hidden(A_200,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_1833])).

tff(c_1857,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_1847])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1724,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_1717,c_8])).

tff(c_1863,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1857,c_1724])).

tff(c_1867,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1763])).

tff(c_1932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1923,c_1867])).

tff(c_1934,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1922])).

tff(c_1950,plain,(
    ! [A_203,B_204,D_205] :
      ( r2_relset_1(A_203,B_204,D_205,D_205)
      | ~ m1_subset_1(D_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2023,plain,(
    ! [B_217,D_218] :
      ( r2_relset_1('#skF_3',B_217,D_218,D_218)
      | ~ m1_subset_1(D_218,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1729,c_1950])).

tff(c_2032,plain,(
    ! [B_217] : r2_relset_1('#skF_3',B_217,'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1934,c_2023])).

tff(c_1762,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_60])).

tff(c_1835,plain,(
    ! [A_199] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_199,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1762,c_1828])).

tff(c_1878,plain,(
    ! [A_201] : ~ r2_hidden(A_201,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1717,c_1835])).

tff(c_1888,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1878])).

tff(c_1894,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1888,c_1724])).

tff(c_1870,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_50])).

tff(c_1966,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1894,c_1870])).

tff(c_2039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2032,c_1966])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.68  
% 3.80/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.68  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.80/1.68  
% 3.80/1.68  %Foreground sorts:
% 3.80/1.68  
% 3.80/1.68  
% 3.80/1.68  %Background operators:
% 3.80/1.68  
% 3.80/1.68  
% 3.80/1.68  %Foreground operators:
% 3.80/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.80/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.80/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.80/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.80/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.68  
% 4.07/1.70  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 4.07/1.70  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.07/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.07/1.70  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.07/1.70  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.07/1.70  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.07/1.70  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.07/1.70  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.07/1.70  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.07/1.70  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.07/1.70  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.07/1.70  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.07/1.70  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_1612, plain, (![A_181, B_182, D_183]: (r2_relset_1(A_181, B_182, D_183, D_183) | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.70  tff(c_1623, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_1612])).
% 4.07/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/1.70  tff(c_223, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.70  tff(c_241, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_223])).
% 4.07/1.70  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_128, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.07/1.70  tff(c_144, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_128])).
% 4.07/1.70  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_480, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.07/1.70  tff(c_505, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_480])).
% 4.07/1.70  tff(c_731, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.07/1.70  tff(c_742, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_731])).
% 4.07/1.70  tff(c_758, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_505, c_742])).
% 4.07/1.70  tff(c_763, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_758])).
% 4.07/1.70  tff(c_145, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_128])).
% 4.07/1.70  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_506, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_480])).
% 4.07/1.70  tff(c_745, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_731])).
% 4.07/1.70  tff(c_761, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_506, c_745])).
% 4.07/1.70  tff(c_769, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_761])).
% 4.07/1.70  tff(c_20, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~v1_xboole_0(B_10) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.07/1.70  tff(c_122, plain, (![E_50]: (k1_funct_1('#skF_5', E_50)=k1_funct_1('#skF_6', E_50) | ~m1_subset_1(E_50, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_127, plain, (![B_10]: (k1_funct_1('#skF_5', B_10)=k1_funct_1('#skF_6', B_10) | ~v1_xboole_0(B_10) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_122])).
% 4.07/1.70  tff(c_169, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_127])).
% 4.07/1.70  tff(c_944, plain, (![A_140, B_141]: (r2_hidden('#skF_2'(A_140, B_141), k1_relat_1(A_140)) | B_141=A_140 | k1_relat_1(B_141)!=k1_relat_1(A_140) | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.07/1.70  tff(c_953, plain, (![B_141]: (r2_hidden('#skF_2'('#skF_6', B_141), '#skF_3') | B_141='#skF_6' | k1_relat_1(B_141)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_141) | ~v1_relat_1(B_141) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_769, c_944])).
% 4.07/1.70  tff(c_998, plain, (![B_148]: (r2_hidden('#skF_2'('#skF_6', B_148), '#skF_3') | B_148='#skF_6' | k1_relat_1(B_148)!='#skF_3' | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_58, c_769, c_953])).
% 4.07/1.70  tff(c_16, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~r2_hidden(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.07/1.70  tff(c_1001, plain, (![B_148]: (m1_subset_1('#skF_2'('#skF_6', B_148), '#skF_3') | v1_xboole_0('#skF_3') | B_148='#skF_6' | k1_relat_1(B_148)!='#skF_3' | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_998, c_16])).
% 4.07/1.70  tff(c_1142, plain, (![B_156]: (m1_subset_1('#skF_2'('#skF_6', B_156), '#skF_3') | B_156='#skF_6' | k1_relat_1(B_156)!='#skF_3' | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(negUnitSimplification, [status(thm)], [c_169, c_1001])).
% 4.07/1.70  tff(c_52, plain, (![E_37]: (k1_funct_1('#skF_5', E_37)=k1_funct_1('#skF_6', E_37) | ~m1_subset_1(E_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_1151, plain, (![B_157]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_157))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_157)) | B_157='#skF_6' | k1_relat_1(B_157)!='#skF_3' | ~v1_funct_1(B_157) | ~v1_relat_1(B_157))), inference(resolution, [status(thm)], [c_1142, c_52])).
% 4.07/1.70  tff(c_26, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_2'(A_14, B_18))!=k1_funct_1(A_14, '#skF_2'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.07/1.70  tff(c_1158, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1151, c_26])).
% 4.07/1.70  tff(c_1165, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_64, c_763, c_145, c_58, c_769, c_763, c_1158])).
% 4.07/1.70  tff(c_50, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.07/1.70  tff(c_1176, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1165, c_50])).
% 4.07/1.70  tff(c_1186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_1176])).
% 4.07/1.70  tff(c_1187, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_761])).
% 4.07/1.70  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.07/1.70  tff(c_1216, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_6])).
% 4.07/1.70  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.07/1.70  tff(c_1215, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_1187, c_12])).
% 4.07/1.70  tff(c_207, plain, (![C_62, B_63, A_64]: (~v1_xboole_0(C_62) | ~m1_subset_1(B_63, k1_zfmisc_1(C_62)) | ~r2_hidden(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.07/1.70  tff(c_220, plain, (![A_64]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_64, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_207])).
% 4.07/1.70  tff(c_222, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_220])).
% 4.07/1.70  tff(c_1243, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_222])).
% 4.07/1.70  tff(c_1248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1243])).
% 4.07/1.70  tff(c_1249, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_758])).
% 4.07/1.70  tff(c_1278, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_6])).
% 4.07/1.70  tff(c_1277, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1249, c_12])).
% 4.07/1.70  tff(c_1302, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1277, c_222])).
% 4.07/1.70  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1302])).
% 4.07/1.70  tff(c_1309, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_220])).
% 4.07/1.70  tff(c_221, plain, (![A_64]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_64, '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_207])).
% 4.07/1.70  tff(c_1542, plain, (![A_178]: (~r2_hidden(A_178, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1309, c_221])).
% 4.07/1.70  tff(c_1552, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_1542])).
% 4.07/1.70  tff(c_1310, plain, (![A_164]: (~r2_hidden(A_164, '#skF_5'))), inference(splitRight, [status(thm)], [c_220])).
% 4.07/1.70  tff(c_1320, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1310])).
% 4.07/1.70  tff(c_92, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | B_42=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.07/1.70  tff(c_95, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_6, c_92])).
% 4.07/1.70  tff(c_1326, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1320, c_95])).
% 4.07/1.70  tff(c_1575, plain, (![A_180]: (A_180='#skF_5' | ~v1_xboole_0(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_95])).
% 4.07/1.70  tff(c_1585, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1552, c_1575])).
% 4.07/1.70  tff(c_1600, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1585, c_50])).
% 4.07/1.70  tff(c_1715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1623, c_1600])).
% 4.07/1.70  tff(c_1717, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_127])).
% 4.07/1.70  tff(c_1723, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1717, c_95])).
% 4.07/1.70  tff(c_38, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.07/1.70  tff(c_67, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 4.07/1.70  tff(c_1922, plain, (![A_30]: (v1_funct_2('#skF_3', A_30, '#skF_3') | A_30='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_1723, c_1723, c_1723, c_1723, c_67])).
% 4.07/1.70  tff(c_1923, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1922])).
% 4.07/1.70  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.07/1.70  tff(c_1729, plain, (![B_8]: (k2_zfmisc_1('#skF_3', B_8)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_1723, c_14])).
% 4.07/1.70  tff(c_1763, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_54])).
% 4.07/1.70  tff(c_1828, plain, (![C_197, B_198, A_199]: (~v1_xboole_0(C_197) | ~m1_subset_1(B_198, k1_zfmisc_1(C_197)) | ~r2_hidden(A_199, B_198))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.07/1.70  tff(c_1833, plain, (![A_199]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_199, '#skF_6'))), inference(resolution, [status(thm)], [c_1763, c_1828])).
% 4.07/1.70  tff(c_1847, plain, (![A_200]: (~r2_hidden(A_200, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_1833])).
% 4.07/1.70  tff(c_1857, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_1847])).
% 4.07/1.70  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.07/1.70  tff(c_1724, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_1717, c_8])).
% 4.07/1.70  tff(c_1863, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_1857, c_1724])).
% 4.07/1.70  tff(c_1867, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1763])).
% 4.07/1.70  tff(c_1932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1923, c_1867])).
% 4.07/1.70  tff(c_1934, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1922])).
% 4.07/1.70  tff(c_1950, plain, (![A_203, B_204, D_205]: (r2_relset_1(A_203, B_204, D_205, D_205) | ~m1_subset_1(D_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.70  tff(c_2023, plain, (![B_217, D_218]: (r2_relset_1('#skF_3', B_217, D_218, D_218) | ~m1_subset_1(D_218, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1729, c_1950])).
% 4.07/1.70  tff(c_2032, plain, (![B_217]: (r2_relset_1('#skF_3', B_217, '#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_1934, c_2023])).
% 4.07/1.70  tff(c_1762, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_60])).
% 4.07/1.70  tff(c_1835, plain, (![A_199]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_199, '#skF_5'))), inference(resolution, [status(thm)], [c_1762, c_1828])).
% 4.07/1.70  tff(c_1878, plain, (![A_201]: (~r2_hidden(A_201, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1717, c_1835])).
% 4.07/1.70  tff(c_1888, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1878])).
% 4.07/1.70  tff(c_1894, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1888, c_1724])).
% 4.07/1.70  tff(c_1870, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_50])).
% 4.07/1.70  tff(c_1966, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1894, c_1870])).
% 4.07/1.70  tff(c_2039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2032, c_1966])).
% 4.07/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.70  
% 4.07/1.70  Inference rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Ref     : 1
% 4.07/1.70  #Sup     : 406
% 4.07/1.70  #Fact    : 0
% 4.07/1.70  #Define  : 0
% 4.07/1.70  #Split   : 12
% 4.07/1.70  #Chain   : 0
% 4.07/1.70  #Close   : 0
% 4.07/1.70  
% 4.07/1.70  Ordering : KBO
% 4.07/1.70  
% 4.07/1.70  Simplification rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Subsume      : 81
% 4.07/1.70  #Demod        : 450
% 4.07/1.70  #Tautology    : 215
% 4.07/1.70  #SimpNegUnit  : 47
% 4.07/1.70  #BackRed      : 143
% 4.07/1.70  
% 4.07/1.70  #Partial instantiations: 0
% 4.07/1.70  #Strategies tried      : 1
% 4.07/1.70  
% 4.07/1.70  Timing (in seconds)
% 4.07/1.70  ----------------------
% 4.07/1.70  Preprocessing        : 0.35
% 4.07/1.70  Parsing              : 0.19
% 4.07/1.70  CNF conversion       : 0.02
% 4.07/1.70  Main loop            : 0.55
% 4.07/1.70  Inferencing          : 0.18
% 4.07/1.70  Reduction            : 0.18
% 4.07/1.70  Demodulation         : 0.12
% 4.07/1.70  BG Simplification    : 0.03
% 4.07/1.70  Subsumption          : 0.10
% 4.07/1.71  Abstraction          : 0.03
% 4.07/1.71  MUC search           : 0.00
% 4.07/1.71  Cooper               : 0.00
% 4.07/1.71  Total                : 0.94
% 4.07/1.71  Index Insertion      : 0.00
% 4.07/1.71  Index Deletion       : 0.00
% 4.07/1.71  Index Matching       : 0.00
% 4.07/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
