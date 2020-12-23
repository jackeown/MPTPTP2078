%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 110 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 321 expanded)
%              Number of equality atoms :    8 (  31 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
            & ! [F] :
                ~ ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_301,plain,(
    ! [C_94,B_91,E_92,A_93,D_90] :
      ( k1_funct_1(D_90,'#skF_2'(D_90,B_91,E_92,A_93,C_94)) = E_92
      | ~ r2_hidden(E_92,k7_relset_1(A_93,B_91,D_90,C_94))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2(D_90,A_93,B_91)
      | ~ v1_funct_1(D_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_312,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_7','#skF_3','#skF_5')) = '#skF_7'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_301])).

tff(c_318,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_7','#skF_3','#skF_5')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_312])).

tff(c_190,plain,(
    ! [A_74,E_73,C_75,B_72,D_71] :
      ( r2_hidden('#skF_2'(D_71,B_72,E_73,A_74,C_75),C_75)
      | ~ r2_hidden(E_73,k7_relset_1(A_74,B_72,D_71,C_75))
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_74,B_72)))
      | ~ v1_funct_2(D_71,A_74,B_72)
      | ~ v1_funct_1(D_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_198,plain,(
    ! [E_73,C_75] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',E_73,'#skF_3',C_75),C_75)
      | ~ r2_hidden(E_73,k7_relset_1('#skF_3','#skF_4','#skF_6',C_75))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_514,plain,(
    ! [E_121,C_122] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',E_121,'#skF_3',C_122),C_122)
      | ~ r2_hidden(E_121,k7_relset_1('#skF_3','#skF_4','#skF_6',C_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_198])).

tff(c_28,plain,(
    ! [F_26] :
      ( k1_funct_1('#skF_6',F_26) != '#skF_7'
      | ~ r2_hidden(F_26,'#skF_5')
      | ~ m1_subset_1(F_26,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_604,plain,(
    ! [E_130] :
      ( k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4',E_130,'#skF_3','#skF_5')) != '#skF_7'
      | ~ m1_subset_1('#skF_2'('#skF_6','#skF_4',E_130,'#skF_3','#skF_5'),'#skF_3')
      | ~ r2_hidden(E_130,k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_514,c_28])).

tff(c_623,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_6','#skF_4','#skF_7','#skF_3','#skF_5')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_6','#skF_4','#skF_7','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_604])).

tff(c_632,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6','#skF_4','#skF_7','#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_623])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_140,plain,(
    ! [B_59,A_61,C_62,E_60,D_58] :
      ( r2_hidden('#skF_2'(D_58,B_59,E_60,A_61,C_62),A_61)
      | ~ r2_hidden(E_60,k7_relset_1(A_61,B_59,D_58,C_62))
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_61,B_59)))
      | ~ v1_funct_2(D_58,A_61,B_59)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_148,plain,(
    ! [E_60,C_62] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',E_60,'#skF_3',C_62),'#skF_3')
      | ~ r2_hidden(E_60,k7_relset_1('#skF_3','#skF_4','#skF_6',C_62))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_404,plain,(
    ! [E_109,C_110] :
      ( r2_hidden('#skF_2'('#skF_6','#skF_4',E_109,'#skF_3',C_110),'#skF_3')
      | ~ r2_hidden(E_109,k7_relset_1('#skF_3','#skF_4','#skF_6',C_110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_148])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,(
    ! [B_9,A_54,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_54,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_412,plain,(
    ! [B_9,E_109,C_110] :
      ( ~ v1_xboole_0(B_9)
      | ~ r1_tarski('#skF_3',B_9)
      | ~ r2_hidden(E_109,k7_relset_1('#skF_3','#skF_4','#skF_6',C_110)) ) ),
    inference(resolution,[status(thm)],[c_404,c_127])).

tff(c_415,plain,(
    ! [E_109,C_110] : ~ r2_hidden(E_109,k7_relset_1('#skF_3','#skF_4','#skF_6',C_110)) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_30])).

tff(c_419,plain,(
    ! [B_111] :
      ( ~ v1_xboole_0(B_111)
      | ~ r1_tarski('#skF_3',B_111) ) ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_429,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_419])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ r2_hidden(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_414,plain,(
    ! [E_109,C_110] :
      ( m1_subset_1('#skF_2'('#skF_6','#skF_4',E_109,'#skF_3',C_110),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r2_hidden(E_109,k7_relset_1('#skF_3','#skF_4','#skF_6',C_110)) ) ),
    inference(resolution,[status(thm)],[c_404,c_8])).

tff(c_2037,plain,(
    ! [E_247,C_248] :
      ( m1_subset_1('#skF_2'('#skF_6','#skF_4',E_247,'#skF_3',C_248),'#skF_3')
      | ~ r2_hidden(E_247,k7_relset_1('#skF_3','#skF_4','#skF_6',C_248)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_414])).

tff(c_2068,plain,(
    m1_subset_1('#skF_2'('#skF_6','#skF_4','#skF_7','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_2037])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_2068])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:03:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.72  
% 4.19/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.72  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 4.19/1.72  
% 4.19/1.72  %Foreground sorts:
% 4.19/1.72  
% 4.19/1.72  
% 4.19/1.72  %Background operators:
% 4.19/1.72  
% 4.19/1.72  
% 4.19/1.72  %Foreground operators:
% 4.19/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.19/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.19/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.19/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.19/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.19/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.19/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.19/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.19/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.19/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.19/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.19/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.19/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.19/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.19/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.19/1.72  
% 4.19/1.73  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.19/1.73  tff(f_74, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 4.19/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.19/1.73  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.19/1.73  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.19/1.73  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.19/1.73  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.19/1.73  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.19/1.73  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.19/1.73  tff(c_30, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.19/1.73  tff(c_301, plain, (![C_94, B_91, E_92, A_93, D_90]: (k1_funct_1(D_90, '#skF_2'(D_90, B_91, E_92, A_93, C_94))=E_92 | ~r2_hidden(E_92, k7_relset_1(A_93, B_91, D_90, C_94)) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_2(D_90, A_93, B_91) | ~v1_funct_1(D_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.19/1.73  tff(c_312, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_7', '#skF_3', '#skF_5'))='#skF_7' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_301])).
% 4.19/1.73  tff(c_318, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_7', '#skF_3', '#skF_5'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_312])).
% 4.19/1.73  tff(c_190, plain, (![A_74, E_73, C_75, B_72, D_71]: (r2_hidden('#skF_2'(D_71, B_72, E_73, A_74, C_75), C_75) | ~r2_hidden(E_73, k7_relset_1(A_74, B_72, D_71, C_75)) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_74, B_72))) | ~v1_funct_2(D_71, A_74, B_72) | ~v1_funct_1(D_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.19/1.73  tff(c_198, plain, (![E_73, C_75]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', E_73, '#skF_3', C_75), C_75) | ~r2_hidden(E_73, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_75)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_190])).
% 4.19/1.73  tff(c_514, plain, (![E_121, C_122]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', E_121, '#skF_3', C_122), C_122) | ~r2_hidden(E_121, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_122)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_198])).
% 4.19/1.73  tff(c_28, plain, (![F_26]: (k1_funct_1('#skF_6', F_26)!='#skF_7' | ~r2_hidden(F_26, '#skF_5') | ~m1_subset_1(F_26, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.19/1.73  tff(c_604, plain, (![E_130]: (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', E_130, '#skF_3', '#skF_5'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_6', '#skF_4', E_130, '#skF_3', '#skF_5'), '#skF_3') | ~r2_hidden(E_130, k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_514, c_28])).
% 4.19/1.73  tff(c_623, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_6', '#skF_4', '#skF_7', '#skF_3', '#skF_5'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_6', '#skF_4', '#skF_7', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_30, c_604])).
% 4.19/1.73  tff(c_632, plain, (~m1_subset_1('#skF_2'('#skF_6', '#skF_4', '#skF_7', '#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_623])).
% 4.19/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.19/1.73  tff(c_93, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.19/1.73  tff(c_103, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_93])).
% 4.19/1.73  tff(c_140, plain, (![B_59, A_61, C_62, E_60, D_58]: (r2_hidden('#skF_2'(D_58, B_59, E_60, A_61, C_62), A_61) | ~r2_hidden(E_60, k7_relset_1(A_61, B_59, D_58, C_62)) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_61, B_59))) | ~v1_funct_2(D_58, A_61, B_59) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.19/1.73  tff(c_148, plain, (![E_60, C_62]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', E_60, '#skF_3', C_62), '#skF_3') | ~r2_hidden(E_60, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_62)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_140])).
% 4.19/1.73  tff(c_404, plain, (![E_109, C_110]: (r2_hidden('#skF_2'('#skF_6', '#skF_4', E_109, '#skF_3', C_110), '#skF_3') | ~r2_hidden(E_109, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_110)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_148])).
% 4.19/1.73  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.19/1.73  tff(c_118, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.19/1.73  tff(c_127, plain, (![B_9, A_54, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_54, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_118])).
% 4.19/1.73  tff(c_412, plain, (![B_9, E_109, C_110]: (~v1_xboole_0(B_9) | ~r1_tarski('#skF_3', B_9) | ~r2_hidden(E_109, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_110)))), inference(resolution, [status(thm)], [c_404, c_127])).
% 4.19/1.73  tff(c_415, plain, (![E_109, C_110]: (~r2_hidden(E_109, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_110)))), inference(splitLeft, [status(thm)], [c_412])).
% 4.19/1.73  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_30])).
% 4.19/1.73  tff(c_419, plain, (![B_111]: (~v1_xboole_0(B_111) | ~r1_tarski('#skF_3', B_111))), inference(splitRight, [status(thm)], [c_412])).
% 4.19/1.73  tff(c_429, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_103, c_419])).
% 4.19/1.73  tff(c_8, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~r2_hidden(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.19/1.73  tff(c_414, plain, (![E_109, C_110]: (m1_subset_1('#skF_2'('#skF_6', '#skF_4', E_109, '#skF_3', C_110), '#skF_3') | v1_xboole_0('#skF_3') | ~r2_hidden(E_109, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_110)))), inference(resolution, [status(thm)], [c_404, c_8])).
% 4.19/1.73  tff(c_2037, plain, (![E_247, C_248]: (m1_subset_1('#skF_2'('#skF_6', '#skF_4', E_247, '#skF_3', C_248), '#skF_3') | ~r2_hidden(E_247, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_248)))), inference(negUnitSimplification, [status(thm)], [c_429, c_414])).
% 4.19/1.73  tff(c_2068, plain, (m1_subset_1('#skF_2'('#skF_6', '#skF_4', '#skF_7', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_30, c_2037])).
% 4.19/1.73  tff(c_2079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_632, c_2068])).
% 4.19/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.19/1.73  
% 4.19/1.73  Inference rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Ref     : 0
% 4.19/1.73  #Sup     : 466
% 4.19/1.73  #Fact    : 0
% 4.19/1.73  #Define  : 0
% 4.19/1.73  #Split   : 24
% 4.19/1.73  #Chain   : 0
% 4.19/1.73  #Close   : 0
% 4.19/1.73  
% 4.19/1.73  Ordering : KBO
% 4.19/1.73  
% 4.19/1.73  Simplification rules
% 4.19/1.73  ----------------------
% 4.19/1.73  #Subsume      : 193
% 4.19/1.73  #Demod        : 21
% 4.19/1.73  #Tautology    : 29
% 4.19/1.73  #SimpNegUnit  : 71
% 4.19/1.73  #BackRed      : 1
% 4.19/1.73  
% 4.19/1.73  #Partial instantiations: 0
% 4.19/1.73  #Strategies tried      : 1
% 4.19/1.73  
% 4.19/1.73  Timing (in seconds)
% 4.19/1.73  ----------------------
% 4.19/1.74  Preprocessing        : 0.29
% 4.19/1.74  Parsing              : 0.16
% 4.19/1.74  CNF conversion       : 0.02
% 4.19/1.74  Main loop            : 0.70
% 4.19/1.74  Inferencing          : 0.24
% 4.19/1.74  Reduction            : 0.18
% 4.19/1.74  Demodulation         : 0.12
% 4.19/1.74  BG Simplification    : 0.03
% 4.19/1.74  Subsumption          : 0.19
% 4.19/1.74  Abstraction          : 0.03
% 4.19/1.74  MUC search           : 0.00
% 4.19/1.74  Cooper               : 0.00
% 4.19/1.74  Total                : 1.02
% 4.19/1.74  Index Insertion      : 0.00
% 4.19/1.74  Index Deletion       : 0.00
% 4.19/1.74  Index Matching       : 0.00
% 4.19/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
