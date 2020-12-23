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
% DateTime   : Thu Dec  3 10:15:08 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 103 expanded)
%              Number of leaves         :   42 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 188 expanded)
%              Number of equality atoms :   27 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_302,plain,(
    ! [C_105,B_106,A_107] :
      ( v5_relat_1(C_105,B_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_306,plain,(
    v5_relat_1('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_80,c_302])).

tff(c_78,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_272,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_276,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_272])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_308,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_312,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_308])).

tff(c_717,plain,(
    ! [B_165,A_166,C_167] :
      ( k1_xboole_0 = B_165
      | k1_relset_1(A_166,B_165,C_167) = A_166
      | ~ v1_funct_2(C_167,A_166,B_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_720,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_80,c_717])).

tff(c_723,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_312,c_720])).

tff(c_724,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_52,plain,(
    ! [C_28,B_27,A_26] :
      ( m1_subset_1(k1_funct_1(C_28,B_27),A_26)
      | ~ r2_hidden(B_27,k1_relat_1(C_28))
      | ~ v1_funct_1(C_28)
      | ~ v5_relat_1(C_28,A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_728,plain,(
    ! [B_27,A_26] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_27),A_26)
      | ~ r2_hidden(B_27,'#skF_6')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_26)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_52])).

tff(c_744,plain,(
    ! [B_171,A_172] :
      ( m1_subset_1(k1_funct_1('#skF_9',B_171),A_172)
      | ~ r2_hidden(B_171,'#skF_6')
      | ~ v5_relat_1('#skF_9',A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_84,c_728])).

tff(c_34,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_87,plain,(
    ! [B_45,A_46] :
      ( ~ r2_hidden(B_45,A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_34,c_87])).

tff(c_247,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(A_83,B_84)
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_254,plain,(
    ! [A_83,A_13] :
      ( A_83 = A_13
      | v1_xboole_0(k1_tarski(A_13))
      | ~ m1_subset_1(A_83,k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_247,c_32])).

tff(c_261,plain,(
    ! [A_83,A_13] :
      ( A_83 = A_13
      | ~ m1_subset_1(A_83,k1_tarski(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_254])).

tff(c_805,plain,(
    ! [B_173,A_174] :
      ( k1_funct_1('#skF_9',B_173) = A_174
      | ~ r2_hidden(B_173,'#skF_6')
      | ~ v5_relat_1('#skF_9',k1_tarski(A_174)) ) ),
    inference(resolution,[status(thm)],[c_744,c_261])).

tff(c_829,plain,(
    ! [A_175] :
      ( k1_funct_1('#skF_9','#skF_8') = A_175
      | ~ v5_relat_1('#skF_9',k1_tarski(A_175)) ) ),
    inference(resolution,[status(thm)],[c_78,c_805])).

tff(c_832,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_306,c_829])).

tff(c_836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_832])).

tff(c_837,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_112,plain,(
    ! [B_51,A_52] :
      ( ~ r1_tarski(B_51,A_52)
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,(
    ! [C_17] : ~ r1_tarski(k1_tarski(C_17),C_17) ),
    inference(resolution,[status(thm)],[c_34,c_112])).

tff(c_867,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_119])).

tff(c_885,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_867])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.45  
% 3.12/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.12/1.45  
% 3.12/1.45  %Foreground sorts:
% 3.12/1.45  
% 3.12/1.45  
% 3.12/1.45  %Background operators:
% 3.12/1.45  
% 3.12/1.45  
% 3.12/1.45  %Foreground operators:
% 3.12/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.12/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.12/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.12/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.45  tff('#skF_9', type, '#skF_9': $i).
% 3.12/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.12/1.45  tff('#skF_8', type, '#skF_8': $i).
% 3.12/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.12/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.12/1.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.12/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.12/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.45  
% 3.16/1.47  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.16/1.47  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.16/1.47  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.16/1.47  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.47  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.47  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.47  tff(f_77, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.16/1.47  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.16/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.16/1.47  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.16/1.47  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.16/1.47  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.47  tff(c_76, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.47  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.47  tff(c_302, plain, (![C_105, B_106, A_107]: (v5_relat_1(C_105, B_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.47  tff(c_306, plain, (v5_relat_1('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_80, c_302])).
% 3.16/1.47  tff(c_78, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.47  tff(c_272, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.16/1.47  tff(c_276, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_272])).
% 3.16/1.47  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.47  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.47  tff(c_308, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.47  tff(c_312, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_308])).
% 3.16/1.47  tff(c_717, plain, (![B_165, A_166, C_167]: (k1_xboole_0=B_165 | k1_relset_1(A_166, B_165, C_167)=A_166 | ~v1_funct_2(C_167, A_166, B_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.16/1.47  tff(c_720, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_80, c_717])).
% 3.16/1.47  tff(c_723, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_312, c_720])).
% 3.16/1.47  tff(c_724, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_723])).
% 3.16/1.47  tff(c_52, plain, (![C_28, B_27, A_26]: (m1_subset_1(k1_funct_1(C_28, B_27), A_26) | ~r2_hidden(B_27, k1_relat_1(C_28)) | ~v1_funct_1(C_28) | ~v5_relat_1(C_28, A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.47  tff(c_728, plain, (![B_27, A_26]: (m1_subset_1(k1_funct_1('#skF_9', B_27), A_26) | ~r2_hidden(B_27, '#skF_6') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_26) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_724, c_52])).
% 3.16/1.47  tff(c_744, plain, (![B_171, A_172]: (m1_subset_1(k1_funct_1('#skF_9', B_171), A_172) | ~r2_hidden(B_171, '#skF_6') | ~v5_relat_1('#skF_9', A_172))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_84, c_728])).
% 3.16/1.47  tff(c_34, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.47  tff(c_87, plain, (![B_45, A_46]: (~r2_hidden(B_45, A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.47  tff(c_94, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_34, c_87])).
% 3.16/1.47  tff(c_247, plain, (![A_83, B_84]: (r2_hidden(A_83, B_84) | v1_xboole_0(B_84) | ~m1_subset_1(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.47  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.47  tff(c_254, plain, (![A_83, A_13]: (A_83=A_13 | v1_xboole_0(k1_tarski(A_13)) | ~m1_subset_1(A_83, k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_247, c_32])).
% 3.16/1.47  tff(c_261, plain, (![A_83, A_13]: (A_83=A_13 | ~m1_subset_1(A_83, k1_tarski(A_13)))), inference(negUnitSimplification, [status(thm)], [c_94, c_254])).
% 3.16/1.47  tff(c_805, plain, (![B_173, A_174]: (k1_funct_1('#skF_9', B_173)=A_174 | ~r2_hidden(B_173, '#skF_6') | ~v5_relat_1('#skF_9', k1_tarski(A_174)))), inference(resolution, [status(thm)], [c_744, c_261])).
% 3.16/1.47  tff(c_829, plain, (![A_175]: (k1_funct_1('#skF_9', '#skF_8')=A_175 | ~v5_relat_1('#skF_9', k1_tarski(A_175)))), inference(resolution, [status(thm)], [c_78, c_805])).
% 3.16/1.47  tff(c_832, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_306, c_829])).
% 3.16/1.47  tff(c_836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_832])).
% 3.16/1.47  tff(c_837, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_723])).
% 3.16/1.47  tff(c_112, plain, (![B_51, A_52]: (~r1_tarski(B_51, A_52) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.47  tff(c_119, plain, (![C_17]: (~r1_tarski(k1_tarski(C_17), C_17))), inference(resolution, [status(thm)], [c_34, c_112])).
% 3.16/1.47  tff(c_867, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_837, c_119])).
% 3.16/1.47  tff(c_885, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_867])).
% 3.16/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  Inference rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Ref     : 0
% 3.16/1.47  #Sup     : 168
% 3.16/1.47  #Fact    : 2
% 3.16/1.47  #Define  : 0
% 3.16/1.47  #Split   : 1
% 3.16/1.47  #Chain   : 0
% 3.16/1.47  #Close   : 0
% 3.16/1.47  
% 3.16/1.47  Ordering : KBO
% 3.16/1.47  
% 3.16/1.47  Simplification rules
% 3.16/1.47  ----------------------
% 3.16/1.47  #Subsume      : 27
% 3.16/1.47  #Demod        : 74
% 3.16/1.47  #Tautology    : 68
% 3.16/1.47  #SimpNegUnit  : 17
% 3.16/1.47  #BackRed      : 5
% 3.16/1.47  
% 3.16/1.47  #Partial instantiations: 0
% 3.16/1.47  #Strategies tried      : 1
% 3.16/1.47  
% 3.16/1.47  Timing (in seconds)
% 3.16/1.47  ----------------------
% 3.16/1.47  Preprocessing        : 0.35
% 3.16/1.47  Parsing              : 0.18
% 3.16/1.47  CNF conversion       : 0.03
% 3.16/1.47  Main loop            : 0.36
% 3.16/1.47  Inferencing          : 0.12
% 3.16/1.47  Reduction            : 0.11
% 3.16/1.47  Demodulation         : 0.07
% 3.16/1.47  BG Simplification    : 0.02
% 3.16/1.47  Subsumption          : 0.06
% 3.16/1.47  Abstraction          : 0.03
% 3.16/1.47  MUC search           : 0.00
% 3.16/1.47  Cooper               : 0.00
% 3.16/1.47  Total                : 0.74
% 3.16/1.47  Index Insertion      : 0.00
% 3.16/1.47  Index Deletion       : 0.00
% 3.16/1.47  Index Matching       : 0.00
% 3.16/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
