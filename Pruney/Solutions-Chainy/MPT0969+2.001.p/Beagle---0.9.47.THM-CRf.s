%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 151 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 341 expanded)
%              Number of equality atoms :   25 ( 112 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => r2_hidden(B,k1_funct_2(A,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
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
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_69,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_69])).

tff(c_75,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_75])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_91,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    k1_relset_1('#skF_5','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_91])).

tff(c_158,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_158])).

tff(c_164,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_95,c_161])).

tff(c_165,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_26,plain,(
    ! [E_34,B_16] :
      ( r2_hidden(E_34,k1_funct_2(k1_relat_1(E_34),B_16))
      | ~ r1_tarski(k2_relat_1(E_34),B_16)
      | ~ v1_funct_1(E_34)
      | ~ v1_relat_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_170,plain,(
    ! [B_16] :
      ( r2_hidden('#skF_6',k1_funct_2('#skF_5',B_16))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_16)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_26])).

tff(c_180,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_6',k1_funct_2('#skF_5',B_96))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_68,c_170])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_6',k1_funct_2('#skF_5','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_187,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_180,c_62])).

tff(c_195,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_187])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_79,c_195])).

tff(c_201,plain,(
    k1_relat_1('#skF_6') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_22,plain,(
    ! [B_13,C_14] :
      ( k1_relset_1(k1_xboole_0,B_13,C_14) = k1_xboole_0
      | ~ v1_funct_2(C_14,k1_xboole_0,B_13)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_232,plain,(
    ! [B_108,C_109] :
      ( k1_relset_1('#skF_5',B_108,C_109) = '#skF_5'
      | ~ v1_funct_2(C_109,'#skF_5',B_108)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_108))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_200,c_200,c_22])).

tff(c_235,plain,
    ( k1_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_232])).

tff(c_238,plain,(
    k1_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_95,c_235])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.30  
% 2.48/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.48/1.30  
% 2.48/1.30  %Foreground sorts:
% 2.48/1.30  
% 2.48/1.30  
% 2.48/1.30  %Background operators:
% 2.48/1.30  
% 2.48/1.30  
% 2.48/1.30  %Foreground operators:
% 2.48/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.48/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.48/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.48/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.48/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.48/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.48/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.48/1.30  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.48/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.48/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.48/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.30  
% 2.48/1.32  tff(f_88, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => r2_hidden(B, k1_funct_2(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_2)).
% 2.48/1.32  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.48/1.32  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.48/1.32  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.48/1.32  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.48/1.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.48/1.32  tff(f_79, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 2.48/1.32  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.48/1.32  tff(c_69, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.32  tff(c_73, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_69])).
% 2.48/1.32  tff(c_75, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.32  tff(c_79, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_75])).
% 2.48/1.32  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.32  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.48/1.32  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.48/1.32  tff(c_91, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.48/1.32  tff(c_95, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_91])).
% 2.48/1.32  tff(c_158, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.32  tff(c_161, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_158])).
% 2.48/1.32  tff(c_164, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_95, c_161])).
% 2.48/1.32  tff(c_165, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_164])).
% 2.48/1.32  tff(c_26, plain, (![E_34, B_16]: (r2_hidden(E_34, k1_funct_2(k1_relat_1(E_34), B_16)) | ~r1_tarski(k2_relat_1(E_34), B_16) | ~v1_funct_1(E_34) | ~v1_relat_1(E_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.48/1.32  tff(c_170, plain, (![B_16]: (r2_hidden('#skF_6', k1_funct_2('#skF_5', B_16)) | ~r1_tarski(k2_relat_1('#skF_6'), B_16) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_26])).
% 2.48/1.32  tff(c_180, plain, (![B_96]: (r2_hidden('#skF_6', k1_funct_2('#skF_5', B_96)) | ~r1_tarski(k2_relat_1('#skF_6'), B_96))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_68, c_170])).
% 2.48/1.32  tff(c_62, plain, (~r2_hidden('#skF_6', k1_funct_2('#skF_5', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.48/1.32  tff(c_187, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_180, c_62])).
% 2.48/1.32  tff(c_195, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_187])).
% 2.48/1.32  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_79, c_195])).
% 2.48/1.32  tff(c_201, plain, (k1_relat_1('#skF_6')!='#skF_5'), inference(splitRight, [status(thm)], [c_164])).
% 2.48/1.32  tff(c_200, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_164])).
% 2.48/1.32  tff(c_22, plain, (![B_13, C_14]: (k1_relset_1(k1_xboole_0, B_13, C_14)=k1_xboole_0 | ~v1_funct_2(C_14, k1_xboole_0, B_13) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_13))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.48/1.32  tff(c_232, plain, (![B_108, C_109]: (k1_relset_1('#skF_5', B_108, C_109)='#skF_5' | ~v1_funct_2(C_109, '#skF_5', B_108) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_108))))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_200, c_200, c_22])).
% 2.48/1.32  tff(c_235, plain, (k1_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_232])).
% 2.48/1.32  tff(c_238, plain, (k1_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_95, c_235])).
% 2.48/1.32  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_238])).
% 2.48/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.32  
% 2.48/1.32  Inference rules
% 2.48/1.32  ----------------------
% 2.48/1.32  #Ref     : 0
% 2.48/1.32  #Sup     : 34
% 2.48/1.32  #Fact    : 0
% 2.48/1.32  #Define  : 0
% 2.48/1.32  #Split   : 1
% 2.48/1.32  #Chain   : 0
% 2.48/1.32  #Close   : 0
% 2.48/1.32  
% 2.48/1.32  Ordering : KBO
% 2.48/1.32  
% 2.48/1.32  Simplification rules
% 2.48/1.32  ----------------------
% 2.48/1.32  #Subsume      : 1
% 2.48/1.32  #Demod        : 33
% 2.48/1.32  #Tautology    : 13
% 2.48/1.32  #SimpNegUnit  : 1
% 2.48/1.32  #BackRed      : 7
% 2.48/1.32  
% 2.48/1.32  #Partial instantiations: 0
% 2.48/1.32  #Strategies tried      : 1
% 2.48/1.32  
% 2.48/1.32  Timing (in seconds)
% 2.48/1.32  ----------------------
% 2.48/1.32  Preprocessing        : 0.35
% 2.48/1.32  Parsing              : 0.17
% 2.48/1.32  CNF conversion       : 0.03
% 2.48/1.32  Main loop            : 0.21
% 2.48/1.32  Inferencing          : 0.08
% 2.48/1.32  Reduction            : 0.06
% 2.48/1.32  Demodulation         : 0.04
% 2.48/1.32  BG Simplification    : 0.02
% 2.48/1.32  Subsumption          : 0.03
% 2.48/1.32  Abstraction          : 0.02
% 2.48/1.32  MUC search           : 0.00
% 2.48/1.32  Cooper               : 0.00
% 2.48/1.32  Total                : 0.59
% 2.48/1.32  Index Insertion      : 0.00
% 2.48/1.32  Index Deletion       : 0.00
% 2.48/1.32  Index Matching       : 0.00
% 2.48/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
