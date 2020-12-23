%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:24 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 101 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 250 expanded)
%              Number of equality atoms :   32 (  81 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_594,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_1'(A_162,B_163,C_164),B_163)
      | k2_relset_1(A_162,B_163,C_164) = B_163
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_596,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_594])).

tff(c_599,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_596])).

tff(c_44,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_6'(D_32),'#skF_3')
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_68,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_557,plain,(
    ! [B_157,A_158,C_159] :
      ( k1_xboole_0 = B_157
      | k1_relset_1(A_158,B_157,C_159) = A_158
      | ~ v1_funct_2(C_159,A_158,B_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_560,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_557])).

tff(c_563,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72,c_560])).

tff(c_564,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_62,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [D_32] :
      ( k1_funct_1('#skF_5','#skF_6'(D_32)) = D_32
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_82,plain,(
    ! [A_59,C_60] :
      ( r2_hidden(k4_tarski(A_59,k1_funct_1(C_60,A_59)),C_60)
      | ~ r2_hidden(A_59,k1_relat_1(C_60))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [D_32] :
      ( r2_hidden(k4_tarski('#skF_6'(D_32),D_32),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_32),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_82])).

tff(c_100,plain,(
    ! [D_32] :
      ( r2_hidden(k4_tarski('#skF_6'(D_32),D_32),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_32),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40,c_94])).

tff(c_566,plain,(
    ! [D_32] :
      ( r2_hidden(k4_tarski('#skF_6'(D_32),D_32),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_32),'#skF_3')
      | ~ r2_hidden(D_32,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_100])).

tff(c_604,plain,(
    ! [E_165,A_166,B_167,C_168] :
      ( ~ r2_hidden(k4_tarski(E_165,'#skF_1'(A_166,B_167,C_168)),C_168)
      | k2_relset_1(A_166,B_167,C_168) = B_167
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_610,plain,(
    ! [A_169,B_170] :
      ( k2_relset_1(A_169,B_170,'#skF_5') = B_170
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_169,B_170,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_169,B_170,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_566,c_604])).

tff(c_615,plain,(
    ! [A_171,B_172] :
      ( k2_relset_1(A_171,B_172,'#skF_5') = B_172
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ r2_hidden('#skF_1'(A_171,B_172,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_610])).

tff(c_618,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_615])).

tff(c_621,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_618])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_621])).

tff(c_624,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_636,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_2])).

tff(c_641,plain,(
    ! [A_173,B_174,C_175] :
      ( r2_hidden('#skF_1'(A_173,B_174,C_175),B_174)
      | k2_relset_1(A_173,B_174,C_175) = B_174
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_643,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_641])).

tff(c_646,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_643])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( ~ r1_tarski(B_6,A_5)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_663,plain,(
    ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_646,c_10])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.44  
% 2.53/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.45  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 2.53/1.45  
% 2.53/1.45  %Foreground sorts:
% 2.53/1.45  
% 2.53/1.45  
% 2.53/1.45  %Background operators:
% 2.53/1.45  
% 2.53/1.45  
% 2.53/1.45  %Foreground operators:
% 2.53/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.53/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.53/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.53/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.53/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.53/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.53/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.53/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.45  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.53/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.45  
% 2.53/1.46  tff(f_99, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.53/1.46  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.53/1.46  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.53/1.46  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.53/1.46  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.53/1.46  tff(f_37, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.53/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.46  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.46  tff(c_34, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.46  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.46  tff(c_594, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_1'(A_162, B_163, C_164), B_163) | k2_relset_1(A_162, B_163, C_164)=B_163 | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.46  tff(c_596, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_594])).
% 2.53/1.46  tff(c_599, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_596])).
% 2.53/1.46  tff(c_44, plain, (![D_32]: (r2_hidden('#skF_6'(D_32), '#skF_3') | ~r2_hidden(D_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.46  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.46  tff(c_68, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.46  tff(c_72, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.53/1.46  tff(c_557, plain, (![B_157, A_158, C_159]: (k1_xboole_0=B_157 | k1_relset_1(A_158, B_157, C_159)=A_158 | ~v1_funct_2(C_159, A_158, B_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_158, B_157))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.46  tff(c_560, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_557])).
% 2.53/1.46  tff(c_563, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_72, c_560])).
% 2.53/1.46  tff(c_564, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_563])).
% 2.53/1.46  tff(c_62, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.46  tff(c_66, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.53/1.46  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.46  tff(c_42, plain, (![D_32]: (k1_funct_1('#skF_5', '#skF_6'(D_32))=D_32 | ~r2_hidden(D_32, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.53/1.46  tff(c_82, plain, (![A_59, C_60]: (r2_hidden(k4_tarski(A_59, k1_funct_1(C_60, A_59)), C_60) | ~r2_hidden(A_59, k1_relat_1(C_60)) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.46  tff(c_94, plain, (![D_32]: (r2_hidden(k4_tarski('#skF_6'(D_32), D_32), '#skF_5') | ~r2_hidden('#skF_6'(D_32), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_32, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_82])).
% 2.53/1.46  tff(c_100, plain, (![D_32]: (r2_hidden(k4_tarski('#skF_6'(D_32), D_32), '#skF_5') | ~r2_hidden('#skF_6'(D_32), k1_relat_1('#skF_5')) | ~r2_hidden(D_32, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40, c_94])).
% 2.53/1.46  tff(c_566, plain, (![D_32]: (r2_hidden(k4_tarski('#skF_6'(D_32), D_32), '#skF_5') | ~r2_hidden('#skF_6'(D_32), '#skF_3') | ~r2_hidden(D_32, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_564, c_100])).
% 2.53/1.46  tff(c_604, plain, (![E_165, A_166, B_167, C_168]: (~r2_hidden(k4_tarski(E_165, '#skF_1'(A_166, B_167, C_168)), C_168) | k2_relset_1(A_166, B_167, C_168)=B_167 | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.46  tff(c_610, plain, (![A_169, B_170]: (k2_relset_1(A_169, B_170, '#skF_5')=B_170 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~r2_hidden('#skF_6'('#skF_1'(A_169, B_170, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_169, B_170, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_566, c_604])).
% 2.53/1.46  tff(c_615, plain, (![A_171, B_172]: (k2_relset_1(A_171, B_172, '#skF_5')=B_172 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~r2_hidden('#skF_1'(A_171, B_172, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_610])).
% 2.53/1.46  tff(c_618, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_36, c_615])).
% 2.53/1.46  tff(c_621, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_599, c_618])).
% 2.53/1.46  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_621])).
% 2.53/1.46  tff(c_624, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_563])).
% 2.53/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.46  tff(c_636, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_2])).
% 2.53/1.46  tff(c_641, plain, (![A_173, B_174, C_175]: (r2_hidden('#skF_1'(A_173, B_174, C_175), B_174) | k2_relset_1(A_173, B_174, C_175)=B_174 | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.46  tff(c_643, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_641])).
% 2.53/1.46  tff(c_646, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_643])).
% 2.53/1.46  tff(c_10, plain, (![B_6, A_5]: (~r1_tarski(B_6, A_5) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.46  tff(c_663, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_646, c_10])).
% 2.53/1.46  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_636, c_663])).
% 2.53/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.46  
% 2.53/1.46  Inference rules
% 2.53/1.46  ----------------------
% 2.53/1.46  #Ref     : 0
% 2.53/1.46  #Sup     : 106
% 2.53/1.46  #Fact    : 0
% 2.53/1.46  #Define  : 0
% 2.53/1.46  #Split   : 10
% 2.53/1.46  #Chain   : 0
% 2.53/1.46  #Close   : 0
% 2.53/1.46  
% 2.53/1.46  Ordering : KBO
% 2.53/1.46  
% 2.53/1.46  Simplification rules
% 2.53/1.46  ----------------------
% 2.53/1.46  #Subsume      : 39
% 2.53/1.46  #Demod        : 170
% 2.53/1.46  #Tautology    : 33
% 2.53/1.46  #SimpNegUnit  : 14
% 2.53/1.46  #BackRed      : 72
% 2.53/1.46  
% 2.53/1.46  #Partial instantiations: 0
% 2.53/1.46  #Strategies tried      : 1
% 2.53/1.46  
% 2.53/1.46  Timing (in seconds)
% 2.53/1.46  ----------------------
% 2.95/1.46  Preprocessing        : 0.32
% 2.95/1.46  Parsing              : 0.17
% 2.95/1.46  CNF conversion       : 0.02
% 2.95/1.46  Main loop            : 0.33
% 2.95/1.46  Inferencing          : 0.12
% 2.95/1.46  Reduction            : 0.10
% 2.95/1.46  Demodulation         : 0.07
% 2.95/1.46  BG Simplification    : 0.02
% 2.95/1.47  Subsumption          : 0.06
% 2.95/1.47  Abstraction          : 0.02
% 2.95/1.47  MUC search           : 0.00
% 2.95/1.47  Cooper               : 0.00
% 2.95/1.47  Total                : 0.68
% 2.95/1.47  Index Insertion      : 0.00
% 2.95/1.47  Index Deletion       : 0.00
% 2.95/1.47  Index Matching       : 0.00
% 2.95/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
