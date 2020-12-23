%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 351 expanded)
%              Number of leaves         :   30 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 (1027 expanded)
%              Number of equality atoms :   38 ( 261 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_82,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_2)).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44])).

tff(c_46,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( v1_xboole_0(k2_zfmisc_1(A_1,B_2))
      | ~ v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_121,plain,(
    ! [C_49,B_50,A_51] :
      ( ~ v1_xboole_0(C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_187,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_191,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_448,plain,(
    ! [B_83,C_84,A_85] :
      ( k1_xboole_0 = B_83
      | v1_funct_2(C_84,A_85,B_83)
      | k1_relset_1(A_85,B_83,C_84) != A_85
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_457,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_448])).

tff(c_469,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_457])).

tff(c_470,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_469])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_500,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_2])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_500])).

tff(c_505,plain,(
    ! [A_86] : ~ r2_hidden(A_86,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_510,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16,c_505])).

tff(c_24,plain,(
    ! [B_31,C_32,A_30] :
      ( k1_xboole_0 = B_31
      | v1_funct_2(C_32,A_30,B_31)
      | k1_relset_1(A_30,B_31,C_32) != A_30
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_709,plain,(
    ! [B_102,C_103,A_104] :
      ( B_102 = '#skF_5'
      | v1_funct_2(C_103,A_104,B_102)
      | k1_relset_1(A_104,B_102,C_103) != A_104
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_24])).

tff(c_721,plain,
    ( '#skF_5' = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_709])).

tff(c_727,plain,
    ( '#skF_5' = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_721])).

tff(c_728,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_727])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_46] : m1_subset_1('#skF_2'(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_104,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_123,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_51,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_104,c_121])).

tff(c_133,plain,(
    ! [A_52] : ~ r2_hidden(A_52,'#skF_2'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_138,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_133])).

tff(c_519,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_510,c_138])).

tff(c_742,plain,(
    '#skF_2'('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_728,c_519])).

tff(c_32,plain,(
    ! [A_33] : v1_funct_2('#skF_2'(A_33),A_33,A_33) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_771,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_742,c_32])).

tff(c_18,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18])).

tff(c_172,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_140,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_104])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_140])).

tff(c_179,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30 ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_530,plain,(
    ! [A_30] :
      ( v1_funct_2('#skF_5',A_30,'#skF_5')
      | A_30 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_510,c_510,c_179])).

tff(c_911,plain,(
    ! [A_120] :
      ( v1_funct_2('#skF_4',A_120,'#skF_4')
      | A_120 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_728,c_728,c_530])).

tff(c_750,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_52])).

tff(c_915,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_911,c_750])).

tff(c_916,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_750])).

tff(c_920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.43  
% 2.86/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.43  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.86/1.43  
% 2.86/1.43  %Foreground sorts:
% 2.86/1.43  
% 2.86/1.43  
% 2.86/1.43  %Background operators:
% 2.86/1.43  
% 2.86/1.43  
% 2.86/1.43  %Foreground operators:
% 2.86/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.43  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.86/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.43  
% 2.86/1.45  tff(f_110, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.86/1.45  tff(f_64, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.86/1.45  tff(f_30, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.86/1.45  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.86/1.45  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.86/1.45  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.86/1.45  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.86/1.45  tff(f_97, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_funct_2)).
% 2.86/1.45  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.86/1.45  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.86/1.45  tff(c_44, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.86/1.45  tff(c_52, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44])).
% 2.86/1.45  tff(c_46, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.86/1.45  tff(c_16, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.45  tff(c_4, plain, (![A_1, B_2]: (v1_xboole_0(k2_zfmisc_1(A_1, B_2)) | ~v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.86/1.45  tff(c_121, plain, (![C_49, B_50, A_51]: (~v1_xboole_0(C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.45  tff(c_132, plain, (![A_51]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_121])).
% 2.86/1.45  tff(c_187, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_132])).
% 2.86/1.45  tff(c_191, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_187])).
% 2.86/1.45  tff(c_448, plain, (![B_83, C_84, A_85]: (k1_xboole_0=B_83 | v1_funct_2(C_84, A_85, B_83) | k1_relset_1(A_85, B_83, C_84)!=A_85 | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_83))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.45  tff(c_457, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_448])).
% 2.86/1.45  tff(c_469, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_457])).
% 2.86/1.45  tff(c_470, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_469])).
% 2.86/1.45  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.86/1.45  tff(c_500, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_2])).
% 2.86/1.45  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_500])).
% 2.86/1.45  tff(c_505, plain, (![A_86]: (~r2_hidden(A_86, '#skF_5'))), inference(splitRight, [status(thm)], [c_132])).
% 2.86/1.45  tff(c_510, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16, c_505])).
% 2.86/1.45  tff(c_24, plain, (![B_31, C_32, A_30]: (k1_xboole_0=B_31 | v1_funct_2(C_32, A_30, B_31) | k1_relset_1(A_30, B_31, C_32)!=A_30 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.45  tff(c_709, plain, (![B_102, C_103, A_104]: (B_102='#skF_5' | v1_funct_2(C_103, A_104, B_102) | k1_relset_1(A_104, B_102, C_103)!=A_104 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_24])).
% 2.86/1.45  tff(c_721, plain, ('#skF_5'='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_709])).
% 2.86/1.45  tff(c_727, plain, ('#skF_5'='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_721])).
% 2.86/1.45  tff(c_728, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_727])).
% 2.86/1.45  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.86/1.45  tff(c_100, plain, (![A_46]: (m1_subset_1('#skF_2'(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.45  tff(c_104, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_100])).
% 2.86/1.45  tff(c_123, plain, (![A_51]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_51, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_104, c_121])).
% 2.86/1.45  tff(c_133, plain, (![A_52]: (~r2_hidden(A_52, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_123])).
% 2.86/1.45  tff(c_138, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_133])).
% 2.86/1.45  tff(c_519, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_510, c_138])).
% 2.86/1.45  tff(c_742, plain, ('#skF_2'('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_728, c_728, c_519])).
% 2.86/1.45  tff(c_32, plain, (![A_33]: (v1_funct_2('#skF_2'(A_33), A_33, A_33))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.45  tff(c_771, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_742, c_32])).
% 2.86/1.45  tff(c_18, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.45  tff(c_56, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18])).
% 2.86/1.45  tff(c_172, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_56])).
% 2.86/1.45  tff(c_140, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_104])).
% 2.86/1.45  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_140])).
% 2.86/1.45  tff(c_179, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30)), inference(splitRight, [status(thm)], [c_56])).
% 2.86/1.45  tff(c_530, plain, (![A_30]: (v1_funct_2('#skF_5', A_30, '#skF_5') | A_30='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_510, c_510, c_179])).
% 2.86/1.45  tff(c_911, plain, (![A_120]: (v1_funct_2('#skF_4', A_120, '#skF_4') | A_120='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_728, c_728, c_728, c_530])).
% 2.86/1.45  tff(c_750, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_728, c_52])).
% 2.86/1.45  tff(c_915, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_911, c_750])).
% 2.86/1.45  tff(c_916, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_915, c_750])).
% 2.86/1.45  tff(c_920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_771, c_916])).
% 2.86/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  Inference rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Ref     : 0
% 2.86/1.45  #Sup     : 175
% 2.86/1.45  #Fact    : 0
% 2.86/1.45  #Define  : 0
% 2.86/1.45  #Split   : 3
% 2.86/1.45  #Chain   : 0
% 2.86/1.45  #Close   : 0
% 2.86/1.45  
% 2.86/1.45  Ordering : KBO
% 2.86/1.45  
% 2.86/1.45  Simplification rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Subsume      : 20
% 2.86/1.45  #Demod        : 301
% 2.86/1.45  #Tautology    : 120
% 2.86/1.45  #SimpNegUnit  : 4
% 2.86/1.45  #BackRed      : 71
% 2.86/1.45  
% 2.86/1.45  #Partial instantiations: 0
% 2.86/1.45  #Strategies tried      : 1
% 2.86/1.45  
% 2.86/1.45  Timing (in seconds)
% 2.86/1.45  ----------------------
% 2.86/1.45  Preprocessing        : 0.30
% 2.86/1.45  Parsing              : 0.17
% 2.86/1.45  CNF conversion       : 0.02
% 2.86/1.45  Main loop            : 0.37
% 2.86/1.45  Inferencing          : 0.13
% 2.86/1.45  Reduction            : 0.13
% 2.86/1.45  Demodulation         : 0.09
% 2.86/1.45  BG Simplification    : 0.02
% 2.86/1.45  Subsumption          : 0.06
% 2.86/1.45  Abstraction          : 0.02
% 2.86/1.45  MUC search           : 0.00
% 2.86/1.45  Cooper               : 0.00
% 2.86/1.45  Total                : 0.71
% 2.86/1.45  Index Insertion      : 0.00
% 2.86/1.45  Index Deletion       : 0.00
% 2.86/1.45  Index Matching       : 0.00
% 2.86/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
