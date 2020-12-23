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
% DateTime   : Thu Dec  3 10:11:28 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 259 expanded)
%              Number of equality atoms :   34 (  83 expanded)
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

tff(f_112,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_513,plain,(
    ! [A_147,B_148,C_149] :
      ( r2_hidden('#skF_1'(A_147,B_148,C_149),B_148)
      | k2_relset_1(A_147,B_148,C_149) = B_148
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_515,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_513])).

tff(c_518,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_515])).

tff(c_48,plain,(
    ! [D_36] :
      ( r2_hidden('#skF_6'(D_36),'#skF_3')
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_74])).

tff(c_461,plain,(
    ! [B_140,A_141,C_142] :
      ( k1_xboole_0 = B_140
      | k1_relset_1(A_141,B_140,C_142) = A_141
      | ~ v1_funct_2(C_142,A_141,B_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_464,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_461])).

tff(c_467,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_78,c_464])).

tff(c_468,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_73,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_70])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    ! [D_36] :
      ( k1_funct_1('#skF_5','#skF_6'(D_36)) = D_36
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_91,plain,(
    ! [B_58,A_59] :
      ( r2_hidden(k4_tarski(B_58,k1_funct_1(A_59,B_58)),A_59)
      | ~ r2_hidden(B_58,k1_relat_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski('#skF_6'(D_36),D_36),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_36),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_91])).

tff(c_100,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski('#skF_6'(D_36),D_36),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_36),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_44,c_97])).

tff(c_470,plain,(
    ! [D_36] :
      ( r2_hidden(k4_tarski('#skF_6'(D_36),D_36),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_36),'#skF_3')
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_100])).

tff(c_524,plain,(
    ! [E_150,A_151,B_152,C_153] :
      ( ~ r2_hidden(k4_tarski(E_150,'#skF_1'(A_151,B_152,C_153)),C_153)
      | k2_relset_1(A_151,B_152,C_153) = B_152
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_631,plain,(
    ! [A_185,B_186] :
      ( k2_relset_1(A_185,B_186,'#skF_5') = B_186
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_185,B_186)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_185,B_186,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_185,B_186,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_470,c_524])).

tff(c_640,plain,(
    ! [A_187,B_188] :
      ( k2_relset_1(A_187,B_188,'#skF_5') = B_188
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ r2_hidden('#skF_1'(A_187,B_188,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_631])).

tff(c_643,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_640])).

tff(c_646,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_643])).

tff(c_648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_646])).

tff(c_649,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_661,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_2])).

tff(c_666,plain,(
    ! [A_189,B_190,C_191] :
      ( r2_hidden('#skF_1'(A_189,B_190,C_191),B_190)
      | k2_relset_1(A_189,B_190,C_191) = B_190
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_668,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_666])).

tff(c_671,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_668])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_682,plain,(
    ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_671,c_16])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_682])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.46  
% 2.96/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.46  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 2.96/1.46  
% 2.96/1.46  %Foreground sorts:
% 2.96/1.46  
% 2.96/1.46  
% 2.96/1.46  %Background operators:
% 2.96/1.46  
% 2.96/1.46  
% 2.96/1.46  %Foreground operators:
% 2.96/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.96/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.96/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.96/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.96/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.96/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.96/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.96/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.46  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.96/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.46  
% 3.07/1.48  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.07/1.48  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 3.07/1.48  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.07/1.48  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.07/1.48  tff(f_36, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.07/1.48  tff(f_34, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.07/1.48  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.07/1.48  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.07/1.48  tff(f_59, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.48  tff(c_38, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.07/1.48  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.07/1.48  tff(c_513, plain, (![A_147, B_148, C_149]: (r2_hidden('#skF_1'(A_147, B_148, C_149), B_148) | k2_relset_1(A_147, B_148, C_149)=B_148 | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.48  tff(c_515, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_513])).
% 3.07/1.48  tff(c_518, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_515])).
% 3.07/1.48  tff(c_48, plain, (![D_36]: (r2_hidden('#skF_6'(D_36), '#skF_3') | ~r2_hidden(D_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.07/1.48  tff(c_42, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.07/1.48  tff(c_74, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.07/1.48  tff(c_78, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_74])).
% 3.07/1.48  tff(c_461, plain, (![B_140, A_141, C_142]: (k1_xboole_0=B_140 | k1_relset_1(A_141, B_140, C_142)=A_141 | ~v1_funct_2(C_142, A_141, B_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.07/1.48  tff(c_464, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_461])).
% 3.07/1.48  tff(c_467, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_78, c_464])).
% 3.07/1.48  tff(c_468, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_467])).
% 3.07/1.48  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.48  tff(c_67, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.07/1.48  tff(c_70, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_67])).
% 3.07/1.48  tff(c_73, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_70])).
% 3.07/1.48  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.07/1.48  tff(c_46, plain, (![D_36]: (k1_funct_1('#skF_5', '#skF_6'(D_36))=D_36 | ~r2_hidden(D_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.07/1.48  tff(c_91, plain, (![B_58, A_59]: (r2_hidden(k4_tarski(B_58, k1_funct_1(A_59, B_58)), A_59) | ~r2_hidden(B_58, k1_relat_1(A_59)) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.07/1.48  tff(c_97, plain, (![D_36]: (r2_hidden(k4_tarski('#skF_6'(D_36), D_36), '#skF_5') | ~r2_hidden('#skF_6'(D_36), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_36, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_91])).
% 3.07/1.48  tff(c_100, plain, (![D_36]: (r2_hidden(k4_tarski('#skF_6'(D_36), D_36), '#skF_5') | ~r2_hidden('#skF_6'(D_36), k1_relat_1('#skF_5')) | ~r2_hidden(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_44, c_97])).
% 3.07/1.48  tff(c_470, plain, (![D_36]: (r2_hidden(k4_tarski('#skF_6'(D_36), D_36), '#skF_5') | ~r2_hidden('#skF_6'(D_36), '#skF_3') | ~r2_hidden(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_100])).
% 3.07/1.48  tff(c_524, plain, (![E_150, A_151, B_152, C_153]: (~r2_hidden(k4_tarski(E_150, '#skF_1'(A_151, B_152, C_153)), C_153) | k2_relset_1(A_151, B_152, C_153)=B_152 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.48  tff(c_631, plain, (![A_185, B_186]: (k2_relset_1(A_185, B_186, '#skF_5')=B_186 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))) | ~r2_hidden('#skF_6'('#skF_1'(A_185, B_186, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_185, B_186, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_470, c_524])).
% 3.07/1.48  tff(c_640, plain, (![A_187, B_188]: (k2_relset_1(A_187, B_188, '#skF_5')=B_188 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~r2_hidden('#skF_1'(A_187, B_188, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_631])).
% 3.07/1.48  tff(c_643, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_40, c_640])).
% 3.07/1.48  tff(c_646, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_518, c_643])).
% 3.07/1.48  tff(c_648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_646])).
% 3.07/1.48  tff(c_649, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_467])).
% 3.07/1.48  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.48  tff(c_661, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_649, c_2])).
% 3.07/1.48  tff(c_666, plain, (![A_189, B_190, C_191]: (r2_hidden('#skF_1'(A_189, B_190, C_191), B_190) | k2_relset_1(A_189, B_190, C_191)=B_190 | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.48  tff(c_668, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_666])).
% 3.07/1.48  tff(c_671, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_668])).
% 3.07/1.48  tff(c_16, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.07/1.48  tff(c_682, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_671, c_16])).
% 3.07/1.48  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_661, c_682])).
% 3.07/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  
% 3.07/1.48  Inference rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Ref     : 0
% 3.07/1.48  #Sup     : 118
% 3.07/1.48  #Fact    : 0
% 3.07/1.48  #Define  : 0
% 3.07/1.48  #Split   : 11
% 3.07/1.48  #Chain   : 0
% 3.07/1.48  #Close   : 0
% 3.07/1.48  
% 3.07/1.48  Ordering : KBO
% 3.07/1.48  
% 3.07/1.48  Simplification rules
% 3.07/1.48  ----------------------
% 3.07/1.48  #Subsume      : 48
% 3.07/1.48  #Demod        : 131
% 3.07/1.48  #Tautology    : 25
% 3.07/1.48  #SimpNegUnit  : 11
% 3.07/1.48  #BackRed      : 47
% 3.07/1.48  
% 3.07/1.48  #Partial instantiations: 0
% 3.07/1.48  #Strategies tried      : 1
% 3.07/1.48  
% 3.07/1.48  Timing (in seconds)
% 3.07/1.48  ----------------------
% 3.07/1.48  Preprocessing        : 0.33
% 3.07/1.48  Parsing              : 0.17
% 3.07/1.48  CNF conversion       : 0.02
% 3.07/1.48  Main loop            : 0.38
% 3.07/1.48  Inferencing          : 0.14
% 3.07/1.48  Reduction            : 0.11
% 3.07/1.48  Demodulation         : 0.08
% 3.07/1.48  BG Simplification    : 0.02
% 3.07/1.48  Subsumption          : 0.07
% 3.07/1.48  Abstraction          : 0.02
% 3.07/1.48  MUC search           : 0.00
% 3.07/1.49  Cooper               : 0.00
% 3.07/1.49  Total                : 0.74
% 3.07/1.49  Index Insertion      : 0.00
% 3.07/1.49  Index Deletion       : 0.00
% 3.07/1.49  Index Matching       : 0.00
% 3.07/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
