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
% DateTime   : Thu Dec  3 10:15:11 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 100 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 190 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_163,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_167,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_236,plain,(
    ! [B_108,A_109,C_110] :
      ( k1_xboole_0 = B_108
      | k1_relset_1(A_109,B_108,C_110) = A_109
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_239,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_236])).

tff(c_242,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_167,c_239])).

tff(c_243,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_118,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_118])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_148,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_152,plain,(
    v5_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_148])).

tff(c_174,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(k1_funct_1(B_76,A_77),k2_relat_1(B_76))
      | ~ r2_hidden(A_77,k1_relat_1(B_76))
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,k2_relat_1(B_15))
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_188,plain,(
    ! [B_93,A_94,A_95] :
      ( r2_hidden(k1_funct_1(B_93,A_94),A_95)
      | ~ v5_relat_1(B_93,A_95)
      | ~ r2_hidden(A_94,k1_relat_1(B_93))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_174,c_28])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [D_56,B_57,A_58] :
      ( D_56 = B_57
      | D_56 = A_58
      | ~ r2_hidden(D_56,k2_tarski(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_137,plain,(
    ! [D_56,A_8] :
      ( D_56 = A_8
      | D_56 = A_8
      | ~ r2_hidden(D_56,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_128])).

tff(c_207,plain,(
    ! [B_96,A_97,A_98] :
      ( k1_funct_1(B_96,A_97) = A_98
      | ~ v5_relat_1(B_96,k1_tarski(A_98))
      | ~ r2_hidden(A_97,k1_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_188,c_137])).

tff(c_209,plain,(
    ! [A_97] :
      ( k1_funct_1('#skF_6',A_97) = '#skF_4'
      | ~ r2_hidden(A_97,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_152,c_207])).

tff(c_212,plain,(
    ! [A_97] :
      ( k1_funct_1('#skF_6',A_97) = '#skF_4'
      | ~ r2_hidden(A_97,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_62,c_209])).

tff(c_720,plain,(
    ! [A_1412] :
      ( k1_funct_1('#skF_6',A_1412) = '#skF_4'
      | ~ r2_hidden(A_1412,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_212])).

tff(c_727,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_56,c_720])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_727])).

tff(c_733,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_73,plain,(
    ! [D_36,A_37] : r2_hidden(D_36,k2_tarski(A_37,D_36)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_73])).

tff(c_83,plain,(
    ! [B_41,A_42] :
      ( ~ r1_tarski(B_41,A_42)
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_97,plain,(
    ! [A_8] : ~ r1_tarski(k1_tarski(A_8),A_8) ),
    inference(resolution,[status(thm)],[c_76,c_83])).

tff(c_747,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_97])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:13:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.69/1.41  
% 2.69/1.41  %Foreground sorts:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Background operators:
% 2.69/1.41  
% 2.69/1.41  
% 2.69/1.41  %Foreground operators:
% 2.69/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.69/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.69/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.41  
% 2.69/1.42  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.42  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.69/1.42  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.69/1.42  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.69/1.42  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.42  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.42  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.69/1.42  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 2.69/1.42  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.69/1.42  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.69/1.42  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.69/1.42  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.42  tff(c_54, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.69/1.42  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.69/1.42  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.69/1.42  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.69/1.42  tff(c_163, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.42  tff(c_167, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_163])).
% 2.69/1.42  tff(c_236, plain, (![B_108, A_109, C_110]: (k1_xboole_0=B_108 | k1_relset_1(A_109, B_108, C_110)=A_109 | ~v1_funct_2(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.69/1.42  tff(c_239, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_236])).
% 2.69/1.42  tff(c_242, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_167, c_239])).
% 2.69/1.42  tff(c_243, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_242])).
% 2.69/1.42  tff(c_118, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.42  tff(c_122, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_118])).
% 2.69/1.42  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.69/1.42  tff(c_148, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.42  tff(c_152, plain, (v5_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_148])).
% 2.69/1.42  tff(c_174, plain, (![B_76, A_77]: (r2_hidden(k1_funct_1(B_76, A_77), k2_relat_1(B_76)) | ~r2_hidden(A_77, k1_relat_1(B_76)) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.42  tff(c_28, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, k2_relat_1(B_15)) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.42  tff(c_188, plain, (![B_93, A_94, A_95]: (r2_hidden(k1_funct_1(B_93, A_94), A_95) | ~v5_relat_1(B_93, A_95) | ~r2_hidden(A_94, k1_relat_1(B_93)) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_174, c_28])).
% 2.69/1.42  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.42  tff(c_128, plain, (![D_56, B_57, A_58]: (D_56=B_57 | D_56=A_58 | ~r2_hidden(D_56, k2_tarski(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.42  tff(c_137, plain, (![D_56, A_8]: (D_56=A_8 | D_56=A_8 | ~r2_hidden(D_56, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_128])).
% 2.69/1.42  tff(c_207, plain, (![B_96, A_97, A_98]: (k1_funct_1(B_96, A_97)=A_98 | ~v5_relat_1(B_96, k1_tarski(A_98)) | ~r2_hidden(A_97, k1_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_188, c_137])).
% 2.69/1.42  tff(c_209, plain, (![A_97]: (k1_funct_1('#skF_6', A_97)='#skF_4' | ~r2_hidden(A_97, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_152, c_207])).
% 2.69/1.42  tff(c_212, plain, (![A_97]: (k1_funct_1('#skF_6', A_97)='#skF_4' | ~r2_hidden(A_97, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_62, c_209])).
% 2.69/1.42  tff(c_720, plain, (![A_1412]: (k1_funct_1('#skF_6', A_1412)='#skF_4' | ~r2_hidden(A_1412, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_212])).
% 2.69/1.42  tff(c_727, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_56, c_720])).
% 2.69/1.42  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_727])).
% 2.69/1.42  tff(c_733, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 2.69/1.42  tff(c_73, plain, (![D_36, A_37]: (r2_hidden(D_36, k2_tarski(A_37, D_36)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.42  tff(c_76, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_73])).
% 2.69/1.42  tff(c_83, plain, (![B_41, A_42]: (~r1_tarski(B_41, A_42) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.42  tff(c_97, plain, (![A_8]: (~r1_tarski(k1_tarski(A_8), A_8))), inference(resolution, [status(thm)], [c_76, c_83])).
% 2.69/1.42  tff(c_747, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_733, c_97])).
% 2.69/1.42  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_747])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 92
% 2.69/1.42  #Fact    : 2
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 2
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 7
% 2.69/1.42  #Demod        : 18
% 2.69/1.42  #Tautology    : 22
% 2.69/1.42  #SimpNegUnit  : 1
% 2.69/1.42  #BackRed      : 6
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 833
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.32
% 2.69/1.42  Parsing              : 0.17
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.33
% 2.69/1.42  Inferencing          : 0.16
% 2.69/1.42  Reduction            : 0.08
% 2.69/1.42  Demodulation         : 0.05
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.05
% 2.69/1.42  Abstraction          : 0.02
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.68
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
