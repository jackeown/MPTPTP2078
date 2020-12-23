%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:45 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   61 (  90 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 243 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_relat_1(E)
              & v1_funct_1(E) )
           => ( r2_hidden(C,A)
             => ( B = k1_xboole_0
                | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_87,axiom,(
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

tff(c_40,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_51])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_71,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),B_50)
      | k1_relset_1(B_50,A_49,C_51) = B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(B_50,A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_74,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_6'),'#skF_3')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_75,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_107,plain,(
    ! [D_65,A_66,B_67,C_68] :
      ( r2_hidden(k4_tarski(D_65,'#skF_2'(A_66,B_67,C_68,D_65)),C_68)
      | ~ r2_hidden(D_65,B_67)
      | k1_relset_1(B_67,A_66,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(B_67,A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r2_hidden(A_10,k1_relat_1(C_12))
      | ~ r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    ! [D_72,C_73,B_74,A_75] :
      ( r2_hidden(D_72,k1_relat_1(C_73))
      | ~ v1_funct_1(C_73)
      | ~ v1_relat_1(C_73)
      | ~ r2_hidden(D_72,B_74)
      | k1_relset_1(B_74,A_75,C_73) != B_74
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(B_74,A_75))) ) ),
    inference(resolution,[status(thm)],[c_107,c_12])).

tff(c_136,plain,(
    ! [C_76,A_77] :
      ( r2_hidden('#skF_5',k1_relat_1(C_76))
      | ~ v1_funct_1(C_76)
      | ~ v1_relat_1(C_76)
      | k1_relset_1('#skF_3',A_77,C_76) != '#skF_3'
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_77))) ) ),
    inference(resolution,[status(thm)],[c_36,c_126])).

tff(c_139,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_142,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_54,c_46,c_139])).

tff(c_6,plain,(
    ! [B_7,C_9,A_6] :
      ( k1_funct_1(k5_relat_1(B_7,C_9),A_6) = k1_funct_1(C_9,k1_funct_1(B_7,A_6))
      | ~ r2_hidden(A_6,k1_relat_1(B_7))
      | ~ v1_funct_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [C_9] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_9),'#skF_5') = k1_funct_1(C_9,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_142,c_6])).

tff(c_151,plain,(
    ! [C_78] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_78),'#skF_5') = k1_funct_1(C_78,k1_funct_1('#skF_6','#skF_5'))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_146])).

tff(c_32,plain,(
    k1_funct_1(k5_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_160,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_32])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_160])).

tff(c_170,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_171,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_171])).

tff(c_177,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_174])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_34,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.18/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.18/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.30  
% 2.18/1.31  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 2.18/1.31  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.18/1.31  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.18/1.31  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 2.18/1.31  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.18/1.31  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.18/1.31  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.18/1.31  tff(c_40, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_38, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.31  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_48, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.31  tff(c_51, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_48])).
% 2.18/1.31  tff(c_54, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_51])).
% 2.18/1.31  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_71, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_1'(A_49, B_50, C_51), B_50) | k1_relset_1(B_50, A_49, C_51)=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(B_50, A_49))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.31  tff(c_74, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_6'), '#skF_3') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_71])).
% 2.18/1.31  tff(c_75, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_74])).
% 2.18/1.31  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_107, plain, (![D_65, A_66, B_67, C_68]: (r2_hidden(k4_tarski(D_65, '#skF_2'(A_66, B_67, C_68, D_65)), C_68) | ~r2_hidden(D_65, B_67) | k1_relset_1(B_67, A_66, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(B_67, A_66))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.31  tff(c_12, plain, (![A_10, C_12, B_11]: (r2_hidden(A_10, k1_relat_1(C_12)) | ~r2_hidden(k4_tarski(A_10, B_11), C_12) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.31  tff(c_126, plain, (![D_72, C_73, B_74, A_75]: (r2_hidden(D_72, k1_relat_1(C_73)) | ~v1_funct_1(C_73) | ~v1_relat_1(C_73) | ~r2_hidden(D_72, B_74) | k1_relset_1(B_74, A_75, C_73)!=B_74 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(B_74, A_75))))), inference(resolution, [status(thm)], [c_107, c_12])).
% 2.18/1.31  tff(c_136, plain, (![C_76, A_77]: (r2_hidden('#skF_5', k1_relat_1(C_76)) | ~v1_funct_1(C_76) | ~v1_relat_1(C_76) | k1_relset_1('#skF_3', A_77, C_76)!='#skF_3' | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_77))))), inference(resolution, [status(thm)], [c_36, c_126])).
% 2.18/1.31  tff(c_139, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(resolution, [status(thm)], [c_42, c_136])).
% 2.18/1.31  tff(c_142, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_54, c_46, c_139])).
% 2.18/1.31  tff(c_6, plain, (![B_7, C_9, A_6]: (k1_funct_1(k5_relat_1(B_7, C_9), A_6)=k1_funct_1(C_9, k1_funct_1(B_7, A_6)) | ~r2_hidden(A_6, k1_relat_1(B_7)) | ~v1_funct_1(C_9) | ~v1_relat_1(C_9) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.31  tff(c_146, plain, (![C_9]: (k1_funct_1(k5_relat_1('#skF_6', C_9), '#skF_5')=k1_funct_1(C_9, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1(C_9) | ~v1_relat_1(C_9) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_142, c_6])).
% 2.18/1.31  tff(c_151, plain, (![C_78]: (k1_funct_1(k5_relat_1('#skF_6', C_78), '#skF_5')=k1_funct_1(C_78, k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_146])).
% 2.18/1.31  tff(c_32, plain, (k1_funct_1(k5_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_160, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_151, c_32])).
% 2.18/1.31  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_160])).
% 2.18/1.31  tff(c_170, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_74])).
% 2.18/1.31  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_44, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.18/1.31  tff(c_171, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.18/1.31  tff(c_174, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_171])).
% 2.18/1.31  tff(c_177, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_174])).
% 2.18/1.31  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_34, c_177])).
% 2.18/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  Inference rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Ref     : 0
% 2.18/1.31  #Sup     : 25
% 2.18/1.31  #Fact    : 0
% 2.18/1.31  #Define  : 0
% 2.18/1.31  #Split   : 1
% 2.18/1.31  #Chain   : 0
% 2.18/1.31  #Close   : 0
% 2.18/1.31  
% 2.18/1.31  Ordering : KBO
% 2.18/1.31  
% 2.18/1.31  Simplification rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Subsume      : 0
% 2.18/1.31  #Demod        : 13
% 2.18/1.31  #Tautology    : 7
% 2.18/1.31  #SimpNegUnit  : 3
% 2.18/1.31  #BackRed      : 0
% 2.18/1.31  
% 2.18/1.31  #Partial instantiations: 0
% 2.18/1.31  #Strategies tried      : 1
% 2.18/1.31  
% 2.18/1.31  Timing (in seconds)
% 2.18/1.31  ----------------------
% 2.18/1.32  Preprocessing        : 0.32
% 2.18/1.32  Parsing              : 0.18
% 2.18/1.32  CNF conversion       : 0.02
% 2.18/1.32  Main loop            : 0.19
% 2.18/1.32  Inferencing          : 0.07
% 2.18/1.32  Reduction            : 0.05
% 2.18/1.32  Demodulation         : 0.04
% 2.18/1.32  BG Simplification    : 0.02
% 2.18/1.32  Subsumption          : 0.03
% 2.18/1.32  Abstraction          : 0.01
% 2.18/1.32  MUC search           : 0.00
% 2.18/1.32  Cooper               : 0.00
% 2.18/1.32  Total                : 0.54
% 2.18/1.32  Index Insertion      : 0.00
% 2.18/1.32  Index Deletion       : 0.00
% 2.18/1.32  Index Matching       : 0.00
% 2.18/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
