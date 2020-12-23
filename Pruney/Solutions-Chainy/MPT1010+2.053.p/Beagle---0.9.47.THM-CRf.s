%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 103 expanded)
%              Number of leaves         :   38 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  117 ( 204 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

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

tff(f_110,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_151,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_155,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_151])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_213,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_217,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_213])).

tff(c_393,plain,(
    ! [B_152,A_153,C_154] :
      ( k1_xboole_0 = B_152
      | k1_relset_1(A_153,B_152,C_154) = A_153
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_396,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_393])).

tff(c_399,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_217,c_396])).

tff(c_400,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_307,plain,(
    ! [B_142,A_143] :
      ( r2_hidden(k4_tarski(B_142,k1_funct_1(A_143,B_142)),A_143)
      | ~ r2_hidden(B_142,k1_relat_1(A_143))
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [C_22,A_19,B_20] :
      ( r2_hidden(C_22,A_19)
      | ~ r2_hidden(C_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_566,plain,(
    ! [B_193,A_194,A_195] :
      ( r2_hidden(k4_tarski(B_193,k1_funct_1(A_194,B_193)),A_195)
      | ~ m1_subset_1(A_194,k1_zfmisc_1(A_195))
      | ~ r2_hidden(B_193,k1_relat_1(A_194))
      | ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(resolution,[status(thm)],[c_307,c_40])).

tff(c_36,plain,(
    ! [B_16,D_18,A_15,C_17] :
      ( r2_hidden(B_16,D_18)
      | ~ r2_hidden(k4_tarski(A_15,B_16),k2_zfmisc_1(C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_698,plain,(
    ! [A_218,B_219,D_220,C_221] :
      ( r2_hidden(k1_funct_1(A_218,B_219),D_220)
      | ~ m1_subset_1(A_218,k1_zfmisc_1(k2_zfmisc_1(C_221,D_220)))
      | ~ r2_hidden(B_219,k1_relat_1(A_218))
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_566,c_36])).

tff(c_700,plain,(
    ! [B_219] :
      ( r2_hidden(k1_funct_1('#skF_6',B_219),k1_tarski('#skF_4'))
      | ~ r2_hidden(B_219,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_698])).

tff(c_704,plain,(
    ! [B_222] :
      ( r2_hidden(k1_funct_1('#skF_6',B_222),k1_tarski('#skF_4'))
      | ~ r2_hidden(B_222,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_76,c_400,c_700])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,(
    ! [E_115,C_116,B_117,A_118] :
      ( E_115 = C_116
      | E_115 = B_117
      | E_115 = A_118
      | ~ r2_hidden(E_115,k1_enumset1(A_118,B_117,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_258,plain,(
    ! [E_119,B_120,A_121] :
      ( E_119 = B_120
      | E_119 = A_121
      | E_119 = A_121
      | ~ r2_hidden(E_119,k2_tarski(A_121,B_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_239])).

tff(c_267,plain,(
    ! [E_119,A_9] :
      ( E_119 = A_9
      | E_119 = A_9
      | E_119 = A_9
      | ~ r2_hidden(E_119,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_258])).

tff(c_719,plain,(
    ! [B_223] :
      ( k1_funct_1('#skF_6',B_223) = '#skF_4'
      | ~ r2_hidden(B_223,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_704,c_267])).

tff(c_737,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_719])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_737])).

tff(c_746,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_110,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [E_8,A_2,B_3] : r2_hidden(E_8,k1_enumset1(A_2,B_3,E_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [B_63,A_64] : r2_hidden(B_63,k2_tarski(A_64,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_6])).

tff(c_145,plain,(
    ! [A_65] : r2_hidden(A_65,k1_tarski(A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_137])).

tff(c_50,plain,(
    ! [B_29,A_28] :
      ( ~ r1_tarski(B_29,A_28)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_149,plain,(
    ! [A_65] : ~ r1_tarski(k1_tarski(A_65),A_65) ),
    inference(resolution,[status(thm)],[c_145,c_50])).

tff(c_760,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_149])).

tff(c_768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_760])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:36:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.46  
% 3.17/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.17/1.47  
% 3.17/1.47  %Foreground sorts:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Background operators:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Foreground operators:
% 3.17/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.17/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.17/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.47  
% 3.24/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.24/1.48  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.24/1.48  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.48  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.24/1.48  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.24/1.48  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.24/1.48  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.24/1.48  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.24/1.48  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.24/1.48  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.24/1.48  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.24/1.48  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.24/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.48  tff(c_68, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.24/1.48  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.24/1.48  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.24/1.48  tff(c_151, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.24/1.48  tff(c_155, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_151])).
% 3.24/1.48  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.24/1.48  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.24/1.48  tff(c_213, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.24/1.48  tff(c_217, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_213])).
% 3.24/1.48  tff(c_393, plain, (![B_152, A_153, C_154]: (k1_xboole_0=B_152 | k1_relset_1(A_153, B_152, C_154)=A_153 | ~v1_funct_2(C_154, A_153, B_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.24/1.48  tff(c_396, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_393])).
% 3.24/1.48  tff(c_399, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_217, c_396])).
% 3.24/1.48  tff(c_400, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_399])).
% 3.24/1.48  tff(c_307, plain, (![B_142, A_143]: (r2_hidden(k4_tarski(B_142, k1_funct_1(A_143, B_142)), A_143) | ~r2_hidden(B_142, k1_relat_1(A_143)) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.48  tff(c_40, plain, (![C_22, A_19, B_20]: (r2_hidden(C_22, A_19) | ~r2_hidden(C_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.48  tff(c_566, plain, (![B_193, A_194, A_195]: (r2_hidden(k4_tarski(B_193, k1_funct_1(A_194, B_193)), A_195) | ~m1_subset_1(A_194, k1_zfmisc_1(A_195)) | ~r2_hidden(B_193, k1_relat_1(A_194)) | ~v1_funct_1(A_194) | ~v1_relat_1(A_194))), inference(resolution, [status(thm)], [c_307, c_40])).
% 3.24/1.48  tff(c_36, plain, (![B_16, D_18, A_15, C_17]: (r2_hidden(B_16, D_18) | ~r2_hidden(k4_tarski(A_15, B_16), k2_zfmisc_1(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.24/1.48  tff(c_698, plain, (![A_218, B_219, D_220, C_221]: (r2_hidden(k1_funct_1(A_218, B_219), D_220) | ~m1_subset_1(A_218, k1_zfmisc_1(k2_zfmisc_1(C_221, D_220))) | ~r2_hidden(B_219, k1_relat_1(A_218)) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_566, c_36])).
% 3.24/1.48  tff(c_700, plain, (![B_219]: (r2_hidden(k1_funct_1('#skF_6', B_219), k1_tarski('#skF_4')) | ~r2_hidden(B_219, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_698])).
% 3.24/1.48  tff(c_704, plain, (![B_222]: (r2_hidden(k1_funct_1('#skF_6', B_222), k1_tarski('#skF_4')) | ~r2_hidden(B_222, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_76, c_400, c_700])).
% 3.24/1.48  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.48  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.24/1.48  tff(c_239, plain, (![E_115, C_116, B_117, A_118]: (E_115=C_116 | E_115=B_117 | E_115=A_118 | ~r2_hidden(E_115, k1_enumset1(A_118, B_117, C_116)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.48  tff(c_258, plain, (![E_119, B_120, A_121]: (E_119=B_120 | E_119=A_121 | E_119=A_121 | ~r2_hidden(E_119, k2_tarski(A_121, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_239])).
% 3.24/1.48  tff(c_267, plain, (![E_119, A_9]: (E_119=A_9 | E_119=A_9 | E_119=A_9 | ~r2_hidden(E_119, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_258])).
% 3.24/1.48  tff(c_719, plain, (![B_223]: (k1_funct_1('#skF_6', B_223)='#skF_4' | ~r2_hidden(B_223, '#skF_3'))), inference(resolution, [status(thm)], [c_704, c_267])).
% 3.24/1.48  tff(c_737, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_70, c_719])).
% 3.24/1.48  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_737])).
% 3.24/1.48  tff(c_746, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_399])).
% 3.24/1.48  tff(c_110, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.24/1.48  tff(c_6, plain, (![E_8, A_2, B_3]: (r2_hidden(E_8, k1_enumset1(A_2, B_3, E_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.48  tff(c_137, plain, (![B_63, A_64]: (r2_hidden(B_63, k2_tarski(A_64, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_6])).
% 3.24/1.48  tff(c_145, plain, (![A_65]: (r2_hidden(A_65, k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_137])).
% 3.24/1.48  tff(c_50, plain, (![B_29, A_28]: (~r1_tarski(B_29, A_28) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.24/1.48  tff(c_149, plain, (![A_65]: (~r1_tarski(k1_tarski(A_65), A_65))), inference(resolution, [status(thm)], [c_145, c_50])).
% 3.24/1.48  tff(c_760, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_746, c_149])).
% 3.24/1.48  tff(c_768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_760])).
% 3.24/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.48  
% 3.24/1.48  Inference rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Ref     : 0
% 3.24/1.48  #Sup     : 151
% 3.24/1.48  #Fact    : 0
% 3.24/1.48  #Define  : 0
% 3.24/1.48  #Split   : 4
% 3.24/1.48  #Chain   : 0
% 3.24/1.48  #Close   : 0
% 3.24/1.48  
% 3.24/1.48  Ordering : KBO
% 3.24/1.48  
% 3.24/1.48  Simplification rules
% 3.24/1.48  ----------------------
% 3.24/1.48  #Subsume      : 22
% 3.24/1.48  #Demod        : 38
% 3.24/1.48  #Tautology    : 31
% 3.24/1.48  #SimpNegUnit  : 1
% 3.24/1.48  #BackRed      : 4
% 3.24/1.48  
% 3.24/1.48  #Partial instantiations: 0
% 3.24/1.48  #Strategies tried      : 1
% 3.24/1.48  
% 3.24/1.48  Timing (in seconds)
% 3.24/1.48  ----------------------
% 3.24/1.49  Preprocessing        : 0.34
% 3.24/1.49  Parsing              : 0.17
% 3.24/1.49  CNF conversion       : 0.02
% 3.24/1.49  Main loop            : 0.38
% 3.24/1.49  Inferencing          : 0.14
% 3.24/1.49  Reduction            : 0.11
% 3.24/1.49  Demodulation         : 0.08
% 3.24/1.49  BG Simplification    : 0.02
% 3.24/1.49  Subsumption          : 0.08
% 3.24/1.49  Abstraction          : 0.02
% 3.24/1.49  MUC search           : 0.00
% 3.24/1.49  Cooper               : 0.00
% 3.24/1.49  Total                : 0.76
% 3.24/1.49  Index Insertion      : 0.00
% 3.24/1.49  Index Deletion       : 0.00
% 3.24/1.49  Index Matching       : 0.00
% 3.24/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
