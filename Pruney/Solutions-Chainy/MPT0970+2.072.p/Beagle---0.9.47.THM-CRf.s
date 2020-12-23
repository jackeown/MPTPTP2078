%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 133 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 363 expanded)
%              Number of equality atoms :   19 (  70 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_24,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_125,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_relset_1(A_49,B_50,C_51),k1_zfmisc_1(B_50))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_130,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k2_relset_1(A_52,B_53,C_54),B_53)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_141,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_145,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_141,c_8])).

tff(c_149,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_145])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_209,plain,(
    ! [D_62,C_63,A_64,B_65] :
      ( r2_hidden(k1_funct_1(D_62,C_63),k2_relset_1(A_64,B_65,D_62))
      | k1_xboole_0 = B_65
      | ~ r2_hidden(C_63,A_64)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(D_62,A_64,B_65)
      | ~ v1_funct_1(D_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_323,plain,(
    ! [D_84,B_82,C_83,B_85,A_86] :
      ( r2_hidden(k1_funct_1(D_84,C_83),B_85)
      | ~ r1_tarski(k2_relset_1(A_86,B_82,D_84),B_85)
      | k1_xboole_0 = B_82
      | ~ r2_hidden(C_83,A_86)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_82)))
      | ~ v1_funct_2(D_84,A_86,B_82)
      | ~ v1_funct_1(D_84) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_333,plain,(
    ! [C_83] :
      ( r2_hidden(k1_funct_1('#skF_4',C_83),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_83,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_141,c_323])).

tff(c_348,plain,(
    ! [C_83] :
      ( r2_hidden(k1_funct_1('#skF_4',C_83),'#skF_3')
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_83,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_333])).

tff(c_350,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_362,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_14])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_149])).

tff(c_371,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_34,plain,(
    ! [D_21] :
      ( r2_hidden('#skF_5'(D_21),'#skF_2')
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [D_21] :
      ( k1_funct_1('#skF_4','#skF_5'(D_21)) = D_21
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_220,plain,(
    ! [D_21,A_64,B_65] :
      ( r2_hidden(D_21,k2_relset_1(A_64,B_65,'#skF_4'))
      | k1_xboole_0 = B_65
      | ~ r2_hidden('#skF_5'(D_21),A_64)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2('#skF_4',A_64,B_65)
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(D_21,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_209])).

tff(c_241,plain,(
    ! [D_67,A_68,B_69] :
      ( r2_hidden(D_67,k2_relset_1(A_68,B_69,'#skF_4'))
      | k1_xboole_0 = B_69
      | ~ r2_hidden('#skF_5'(D_67),A_68)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2('#skF_4',A_68,B_69)
      | ~ r2_hidden(D_67,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_220])).

tff(c_372,plain,(
    ! [D_87,B_88] :
      ( r2_hidden(D_87,k2_relset_1('#skF_2',B_88,'#skF_4'))
      | k1_xboole_0 = B_88
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_88)))
      | ~ v1_funct_2('#skF_4','#skF_2',B_88)
      | ~ r2_hidden(D_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_241])).

tff(c_377,plain,(
    ! [D_87] :
      ( r2_hidden(D_87,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ r2_hidden(D_87,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_381,plain,(
    ! [D_87] :
      ( r2_hidden(D_87,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(D_87,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_377])).

tff(c_390,plain,(
    ! [D_90] :
      ( r2_hidden(D_90,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(D_90,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_381])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_549,plain,(
    ! [A_109] :
      ( r1_tarski(A_109,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_109,k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_390,c_4])).

tff(c_561,plain,(
    r1_tarski('#skF_3',k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_549])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_149,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:06:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.44  
% 2.68/1.44  %Foreground sorts:
% 2.68/1.44  
% 2.68/1.44  
% 2.68/1.44  %Background operators:
% 2.68/1.44  
% 2.68/1.44  
% 2.68/1.44  %Foreground operators:
% 2.68/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.68/1.44  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.68/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.44  
% 2.68/1.45  tff(f_79, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 2.68/1.45  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.68/1.45  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.68/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.68/1.45  tff(f_60, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.68/1.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.68/1.45  tff(c_24, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.45  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.45  tff(c_125, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_relset_1(A_49, B_50, C_51), k1_zfmisc_1(B_50)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.45  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.45  tff(c_130, plain, (![A_52, B_53, C_54]: (r1_tarski(k2_relset_1(A_52, B_53, C_54), B_53) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(resolution, [status(thm)], [c_125, c_16])).
% 2.68/1.45  tff(c_141, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_26, c_130])).
% 2.68/1.45  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.45  tff(c_145, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_8])).
% 2.68/1.45  tff(c_149, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_24, c_145])).
% 2.68/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.45  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.45  tff(c_28, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.45  tff(c_209, plain, (![D_62, C_63, A_64, B_65]: (r2_hidden(k1_funct_1(D_62, C_63), k2_relset_1(A_64, B_65, D_62)) | k1_xboole_0=B_65 | ~r2_hidden(C_63, A_64) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(D_62, A_64, B_65) | ~v1_funct_1(D_62))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.45  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.45  tff(c_323, plain, (![D_84, B_82, C_83, B_85, A_86]: (r2_hidden(k1_funct_1(D_84, C_83), B_85) | ~r1_tarski(k2_relset_1(A_86, B_82, D_84), B_85) | k1_xboole_0=B_82 | ~r2_hidden(C_83, A_86) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_82))) | ~v1_funct_2(D_84, A_86, B_82) | ~v1_funct_1(D_84))), inference(resolution, [status(thm)], [c_209, c_2])).
% 2.68/1.45  tff(c_333, plain, (![C_83]: (r2_hidden(k1_funct_1('#skF_4', C_83), '#skF_3') | k1_xboole_0='#skF_3' | ~r2_hidden(C_83, '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_141, c_323])).
% 2.68/1.45  tff(c_348, plain, (![C_83]: (r2_hidden(k1_funct_1('#skF_4', C_83), '#skF_3') | k1_xboole_0='#skF_3' | ~r2_hidden(C_83, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_333])).
% 2.68/1.45  tff(c_350, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_348])).
% 2.68/1.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.45  tff(c_362, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_14])).
% 2.68/1.45  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_362, c_149])).
% 2.68/1.45  tff(c_371, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_348])).
% 2.68/1.45  tff(c_34, plain, (![D_21]: (r2_hidden('#skF_5'(D_21), '#skF_2') | ~r2_hidden(D_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.45  tff(c_32, plain, (![D_21]: (k1_funct_1('#skF_4', '#skF_5'(D_21))=D_21 | ~r2_hidden(D_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.45  tff(c_220, plain, (![D_21, A_64, B_65]: (r2_hidden(D_21, k2_relset_1(A_64, B_65, '#skF_4')) | k1_xboole_0=B_65 | ~r2_hidden('#skF_5'(D_21), A_64) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2('#skF_4', A_64, B_65) | ~v1_funct_1('#skF_4') | ~r2_hidden(D_21, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_209])).
% 2.68/1.45  tff(c_241, plain, (![D_67, A_68, B_69]: (r2_hidden(D_67, k2_relset_1(A_68, B_69, '#skF_4')) | k1_xboole_0=B_69 | ~r2_hidden('#skF_5'(D_67), A_68) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2('#skF_4', A_68, B_69) | ~r2_hidden(D_67, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_220])).
% 2.68/1.45  tff(c_372, plain, (![D_87, B_88]: (r2_hidden(D_87, k2_relset_1('#skF_2', B_88, '#skF_4')) | k1_xboole_0=B_88 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_88))) | ~v1_funct_2('#skF_4', '#skF_2', B_88) | ~r2_hidden(D_87, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_241])).
% 2.68/1.45  tff(c_377, plain, (![D_87]: (r2_hidden(D_87, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~r2_hidden(D_87, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_372])).
% 2.68/1.45  tff(c_381, plain, (![D_87]: (r2_hidden(D_87, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(D_87, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_377])).
% 2.68/1.45  tff(c_390, plain, (![D_90]: (r2_hidden(D_90, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(D_90, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_371, c_381])).
% 2.68/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.45  tff(c_549, plain, (![A_109]: (r1_tarski(A_109, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_109, k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_390, c_4])).
% 2.68/1.45  tff(c_561, plain, (r1_tarski('#skF_3', k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_549])).
% 2.68/1.45  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_149, c_561])).
% 2.68/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.45  
% 2.68/1.45  Inference rules
% 2.68/1.45  ----------------------
% 2.68/1.45  #Ref     : 0
% 2.68/1.45  #Sup     : 115
% 2.68/1.45  #Fact    : 0
% 2.68/1.45  #Define  : 0
% 2.68/1.45  #Split   : 6
% 2.68/1.45  #Chain   : 0
% 2.68/1.45  #Close   : 0
% 2.68/1.45  
% 2.68/1.45  Ordering : KBO
% 2.68/1.45  
% 2.68/1.45  Simplification rules
% 2.68/1.45  ----------------------
% 2.68/1.45  #Subsume      : 12
% 2.68/1.45  #Demod        : 52
% 2.68/1.45  #Tautology    : 36
% 2.68/1.45  #SimpNegUnit  : 3
% 2.68/1.45  #BackRed      : 13
% 2.68/1.45  
% 2.68/1.45  #Partial instantiations: 0
% 2.68/1.45  #Strategies tried      : 1
% 2.68/1.45  
% 2.68/1.45  Timing (in seconds)
% 2.68/1.45  ----------------------
% 2.68/1.45  Preprocessing        : 0.31
% 2.68/1.45  Parsing              : 0.18
% 2.68/1.45  CNF conversion       : 0.02
% 2.68/1.45  Main loop            : 0.33
% 2.68/1.45  Inferencing          : 0.12
% 2.68/1.45  Reduction            : 0.09
% 2.68/1.45  Demodulation         : 0.06
% 2.68/1.45  BG Simplification    : 0.02
% 2.68/1.45  Subsumption          : 0.08
% 2.68/1.45  Abstraction          : 0.01
% 2.68/1.45  MUC search           : 0.00
% 2.68/1.45  Cooper               : 0.00
% 2.68/1.45  Total                : 0.67
% 2.68/1.45  Index Insertion      : 0.00
% 2.68/1.45  Index Deletion       : 0.00
% 2.68/1.45  Index Matching       : 0.00
% 2.68/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
