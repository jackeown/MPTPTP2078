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
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 6.74s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 127 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  125 ( 393 expanded)
%              Number of equality atoms :   29 (  93 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k2_relset_1(A_11,B_12,C_13),k1_zfmisc_1(B_12))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r2_hidden('#skF_2'(A_40,B_41),A_40)
      | B_41 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_302,plain,(
    ! [A_89,B_90,A_91] :
      ( r2_hidden('#skF_2'(A_89,B_90),A_91)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_91))
      | r2_hidden('#skF_1'(A_89,B_90),B_90)
      | B_90 = A_89 ) ),
    inference(resolution,[status(thm)],[c_82,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_327,plain,(
    ! [A_89,A_91] :
      ( ~ m1_subset_1(A_89,k1_zfmisc_1(A_91))
      | r2_hidden('#skF_1'(A_89,A_91),A_91)
      | A_91 = A_89 ) ),
    inference(resolution,[status(thm)],[c_302,c_4])).

tff(c_24,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [D_21] :
      ( r2_hidden('#skF_6'(D_21),'#skF_3')
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [D_21] :
      ( k1_funct_1('#skF_5','#skF_6'(D_21)) = D_21
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_229,plain,(
    ! [D_70,C_71,A_72,B_73] :
      ( r2_hidden(k1_funct_1(D_70,C_71),k2_relset_1(A_72,B_73,D_70))
      | k1_xboole_0 = B_73
      | ~ r2_hidden(C_71,A_72)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(D_70,A_72,B_73)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_237,plain,(
    ! [D_21,A_72,B_73] :
      ( r2_hidden(D_21,k2_relset_1(A_72,B_73,'#skF_5'))
      | k1_xboole_0 = B_73
      | ~ r2_hidden('#skF_6'(D_21),A_72)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2('#skF_5',A_72,B_73)
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_229])).

tff(c_463,plain,(
    ! [D_113,A_114,B_115] :
      ( r2_hidden(D_113,k2_relset_1(A_114,B_115,'#skF_5'))
      | k1_xboole_0 = B_115
      | ~ r2_hidden('#skF_6'(D_113),A_114)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_2('#skF_5',A_114,B_115)
      | ~ r2_hidden(D_113,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_237])).

tff(c_505,plain,(
    ! [D_123,B_124] :
      ( r2_hidden(D_123,k2_relset_1('#skF_3',B_124,'#skF_5'))
      | k1_xboole_0 = B_124
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_124)))
      | ~ v1_funct_2('#skF_5','#skF_3',B_124)
      | ~ r2_hidden(D_123,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_463])).

tff(c_507,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ r2_hidden(D_123,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_505])).

tff(c_510,plain,(
    ! [D_123] :
      ( r2_hidden(D_123,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(D_123,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_507])).

tff(c_511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_541,plain,(
    ! [A_125] : r1_tarski('#skF_4',A_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_10])).

tff(c_337,plain,(
    ! [A_92,A_93] :
      ( ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | r2_hidden('#skF_1'(A_92,A_93),A_93)
      | A_93 = A_92 ) ),
    inference(resolution,[status(thm)],[c_302,c_4])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_360,plain,(
    ! [A_93,A_92] :
      ( ~ r1_tarski(A_93,'#skF_1'(A_92,A_93))
      | ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | A_93 = A_92 ) ),
    inference(resolution,[status(thm)],[c_337,c_14])).

tff(c_574,plain,(
    ! [A_126] :
      ( ~ m1_subset_1(A_126,k1_zfmisc_1('#skF_4'))
      | A_126 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_541,c_360])).

tff(c_762,plain,(
    ! [A_161,C_162] :
      ( k2_relset_1(A_161,'#skF_4',C_162) = '#skF_4'
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,'#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_16,c_574])).

tff(c_769,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_762])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_769])).

tff(c_783,plain,(
    ! [D_167] :
      ( r2_hidden(D_167,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ r2_hidden(D_167,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_68,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r2_hidden('#skF_2'(A_38,B_39),A_38)
      | B_39 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_38,B_39,A_5] :
      ( r2_hidden('#skF_2'(A_38,B_39),A_5)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_5))
      | ~ r2_hidden('#skF_1'(A_38,B_39),A_38)
      | B_39 = A_38 ) ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_3813,plain,(
    ! [B_804,A_805] :
      ( r2_hidden('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_804),A_805)
      | ~ m1_subset_1(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(A_805))
      | k2_relset_1('#skF_3','#skF_4','#skF_5') = B_804
      | ~ r2_hidden('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_804),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_783,c_80])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2),B_2)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_814,plain,(
    ! [B_2] :
      ( ~ r2_hidden('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_2),B_2)
      | k2_relset_1('#skF_3','#skF_4','#skF_5') = B_2
      | ~ r2_hidden('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_2),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_783,c_2])).

tff(c_3842,plain,(
    ! [A_806] :
      ( ~ m1_subset_1(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(A_806))
      | k2_relset_1('#skF_3','#skF_4','#skF_5') = A_806
      | ~ r2_hidden('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_806),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3813,c_814])).

tff(c_3874,plain,
    ( ~ m1_subset_1(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1('#skF_4'))
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_327,c_3842])).

tff(c_3886,plain,(
    ~ m1_subset_1(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_3874])).

tff(c_3889,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_16,c_3886])).

tff(c_3893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.74/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.74/2.40  
% 6.74/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.74/2.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1 > #skF_6
% 6.74/2.40  
% 6.74/2.40  %Foreground sorts:
% 6.74/2.40  
% 6.74/2.40  
% 6.74/2.40  %Background operators:
% 6.74/2.40  
% 6.74/2.40  
% 6.74/2.40  %Foreground operators:
% 6.74/2.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.74/2.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.74/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.74/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.74/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.74/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.74/2.40  tff('#skF_5', type, '#skF_5': $i).
% 6.74/2.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.74/2.40  tff('#skF_3', type, '#skF_3': $i).
% 6.74/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.74/2.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.74/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.74/2.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.74/2.40  tff('#skF_4', type, '#skF_4': $i).
% 6.74/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.74/2.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.74/2.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.74/2.40  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.74/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.74/2.40  
% 6.74/2.41  tff(f_81, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 6.74/2.41  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.74/2.41  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 6.74/2.41  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.74/2.41  tff(f_62, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 6.74/2.41  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.74/2.41  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.74/2.41  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.74/2.41  tff(c_16, plain, (![A_11, B_12, C_13]: (m1_subset_1(k2_relset_1(A_11, B_12, C_13), k1_zfmisc_1(B_12)) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.74/2.41  tff(c_20, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.74/2.41  tff(c_82, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), B_41) | r2_hidden('#skF_2'(A_40, B_41), A_40) | B_41=A_40)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.74/2.41  tff(c_12, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.74/2.41  tff(c_302, plain, (![A_89, B_90, A_91]: (r2_hidden('#skF_2'(A_89, B_90), A_91) | ~m1_subset_1(A_89, k1_zfmisc_1(A_91)) | r2_hidden('#skF_1'(A_89, B_90), B_90) | B_90=A_89)), inference(resolution, [status(thm)], [c_82, c_12])).
% 6.74/2.41  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.74/2.41  tff(c_327, plain, (![A_89, A_91]: (~m1_subset_1(A_89, k1_zfmisc_1(A_91)) | r2_hidden('#skF_1'(A_89, A_91), A_91) | A_91=A_89)), inference(resolution, [status(thm)], [c_302, c_4])).
% 6.74/2.41  tff(c_24, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.74/2.41  tff(c_30, plain, (![D_21]: (r2_hidden('#skF_6'(D_21), '#skF_3') | ~r2_hidden(D_21, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.74/2.41  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.74/2.41  tff(c_28, plain, (![D_21]: (k1_funct_1('#skF_5', '#skF_6'(D_21))=D_21 | ~r2_hidden(D_21, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.74/2.41  tff(c_229, plain, (![D_70, C_71, A_72, B_73]: (r2_hidden(k1_funct_1(D_70, C_71), k2_relset_1(A_72, B_73, D_70)) | k1_xboole_0=B_73 | ~r2_hidden(C_71, A_72) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(D_70, A_72, B_73) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.74/2.41  tff(c_237, plain, (![D_21, A_72, B_73]: (r2_hidden(D_21, k2_relset_1(A_72, B_73, '#skF_5')) | k1_xboole_0=B_73 | ~r2_hidden('#skF_6'(D_21), A_72) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2('#skF_5', A_72, B_73) | ~v1_funct_1('#skF_5') | ~r2_hidden(D_21, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_229])).
% 6.74/2.41  tff(c_463, plain, (![D_113, A_114, B_115]: (r2_hidden(D_113, k2_relset_1(A_114, B_115, '#skF_5')) | k1_xboole_0=B_115 | ~r2_hidden('#skF_6'(D_113), A_114) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_2('#skF_5', A_114, B_115) | ~r2_hidden(D_113, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_237])).
% 6.74/2.41  tff(c_505, plain, (![D_123, B_124]: (r2_hidden(D_123, k2_relset_1('#skF_3', B_124, '#skF_5')) | k1_xboole_0=B_124 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_124))) | ~v1_funct_2('#skF_5', '#skF_3', B_124) | ~r2_hidden(D_123, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_463])).
% 6.74/2.41  tff(c_507, plain, (![D_123]: (r2_hidden(D_123, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~r2_hidden(D_123, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_505])).
% 6.74/2.41  tff(c_510, plain, (![D_123]: (r2_hidden(D_123, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | k1_xboole_0='#skF_4' | ~r2_hidden(D_123, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_507])).
% 6.74/2.41  tff(c_511, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_510])).
% 6.74/2.41  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.74/2.41  tff(c_541, plain, (![A_125]: (r1_tarski('#skF_4', A_125))), inference(demodulation, [status(thm), theory('equality')], [c_511, c_10])).
% 6.74/2.41  tff(c_337, plain, (![A_92, A_93]: (~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | r2_hidden('#skF_1'(A_92, A_93), A_93) | A_93=A_92)), inference(resolution, [status(thm)], [c_302, c_4])).
% 6.74/2.41  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.74/2.41  tff(c_360, plain, (![A_93, A_92]: (~r1_tarski(A_93, '#skF_1'(A_92, A_93)) | ~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | A_93=A_92)), inference(resolution, [status(thm)], [c_337, c_14])).
% 6.74/2.41  tff(c_574, plain, (![A_126]: (~m1_subset_1(A_126, k1_zfmisc_1('#skF_4')) | A_126='#skF_4')), inference(resolution, [status(thm)], [c_541, c_360])).
% 6.74/2.41  tff(c_762, plain, (![A_161, C_162]: (k2_relset_1(A_161, '#skF_4', C_162)='#skF_4' | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, '#skF_4'))))), inference(resolution, [status(thm)], [c_16, c_574])).
% 6.74/2.41  tff(c_769, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_762])).
% 6.74/2.41  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_769])).
% 6.74/2.41  tff(c_783, plain, (![D_167]: (r2_hidden(D_167, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~r2_hidden(D_167, '#skF_4'))), inference(splitRight, [status(thm)], [c_510])).
% 6.74/2.41  tff(c_68, plain, (![A_38, B_39]: (~r2_hidden('#skF_1'(A_38, B_39), A_38) | r2_hidden('#skF_2'(A_38, B_39), A_38) | B_39=A_38)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.74/2.41  tff(c_80, plain, (![A_38, B_39, A_5]: (r2_hidden('#skF_2'(A_38, B_39), A_5) | ~m1_subset_1(A_38, k1_zfmisc_1(A_5)) | ~r2_hidden('#skF_1'(A_38, B_39), A_38) | B_39=A_38)), inference(resolution, [status(thm)], [c_68, c_12])).
% 6.74/2.41  tff(c_3813, plain, (![B_804, A_805]: (r2_hidden('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_804), A_805) | ~m1_subset_1(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(A_805)) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=B_804 | ~r2_hidden('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_804), '#skF_4'))), inference(resolution, [status(thm)], [c_783, c_80])).
% 6.74/2.41  tff(c_2, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), A_1) | ~r2_hidden('#skF_2'(A_1, B_2), B_2) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.74/2.41  tff(c_814, plain, (![B_2]: (~r2_hidden('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_2), B_2) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=B_2 | ~r2_hidden('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_2), '#skF_4'))), inference(resolution, [status(thm)], [c_783, c_2])).
% 6.74/2.41  tff(c_3842, plain, (![A_806]: (~m1_subset_1(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(A_806)) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=A_806 | ~r2_hidden('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_806), '#skF_4'))), inference(resolution, [status(thm)], [c_3813, c_814])).
% 6.74/2.41  tff(c_3874, plain, (~m1_subset_1(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4')) | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_327, c_3842])).
% 6.74/2.41  tff(c_3886, plain, (~m1_subset_1(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_3874])).
% 6.74/2.41  tff(c_3889, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_16, c_3886])).
% 6.74/2.41  tff(c_3893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_3889])).
% 6.74/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.74/2.41  
% 6.74/2.41  Inference rules
% 6.74/2.41  ----------------------
% 6.74/2.41  #Ref     : 0
% 6.74/2.41  #Sup     : 832
% 6.74/2.41  #Fact    : 2
% 6.74/2.41  #Define  : 0
% 6.74/2.41  #Split   : 8
% 6.74/2.41  #Chain   : 0
% 6.74/2.41  #Close   : 0
% 6.74/2.41  
% 6.74/2.41  Ordering : KBO
% 6.74/2.41  
% 6.74/2.41  Simplification rules
% 6.74/2.41  ----------------------
% 6.74/2.41  #Subsume      : 394
% 6.74/2.41  #Demod        : 241
% 6.74/2.41  #Tautology    : 92
% 6.74/2.41  #SimpNegUnit  : 16
% 6.74/2.41  #BackRed      : 91
% 6.74/2.41  
% 6.74/2.41  #Partial instantiations: 0
% 6.74/2.41  #Strategies tried      : 1
% 6.74/2.41  
% 6.74/2.41  Timing (in seconds)
% 6.74/2.41  ----------------------
% 6.74/2.42  Preprocessing        : 0.29
% 6.74/2.42  Parsing              : 0.17
% 6.74/2.42  CNF conversion       : 0.02
% 6.74/2.42  Main loop            : 1.32
% 6.74/2.42  Inferencing          : 0.45
% 6.74/2.42  Reduction            : 0.29
% 6.74/2.42  Demodulation         : 0.18
% 6.74/2.42  BG Simplification    : 0.04
% 6.74/2.42  Subsumption          : 0.44
% 6.74/2.42  Abstraction          : 0.05
% 6.74/2.42  MUC search           : 0.00
% 6.74/2.42  Cooper               : 0.00
% 6.74/2.42  Total                : 1.64
% 6.74/2.42  Index Insertion      : 0.00
% 6.74/2.42  Index Deletion       : 0.00
% 6.74/2.42  Index Matching       : 0.00
% 6.74/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
