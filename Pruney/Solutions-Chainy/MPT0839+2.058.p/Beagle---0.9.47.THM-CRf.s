%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:29 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 165 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 328 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_32,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_18,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | k2_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_18])).

tff(c_77,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_78,plain,(
    ! [A_48] :
      ( k2_relat_1(A_48) = k1_xboole_0
      | k1_relat_1(A_48) != k1_xboole_0
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_78])).

tff(c_87,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_81])).

tff(c_128,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_265,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_279,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_265])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [A_71,B_72,A_73] :
      ( m1_subset_1(A_71,B_72)
      | ~ r2_hidden(A_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_149])).

tff(c_161,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1('#skF_1'(A_74),B_75)
      | ~ r1_tarski(A_74,B_75)
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_2,c_157])).

tff(c_51,plain,(
    ! [D_44] :
      ( ~ r2_hidden(D_44,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_44,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_97,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_187,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3')
    | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_97])).

tff(c_231,plain,(
    ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_280,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_231])).

tff(c_289,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_280])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_137,c_289])).

tff(c_294,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_351,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_362,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_351])).

tff(c_366,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_362])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_366])).

tff(c_369,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_512,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_523,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_512])).

tff(c_527,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_523])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_527])).

tff(c_531,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_718,plain,(
    ! [A_185,B_186,C_187] :
      ( k2_relset_1(A_185,B_186,C_187) = k2_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_729,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_718])).

tff(c_733,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_729])).

tff(c_735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:23:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  
% 2.73/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.37  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.73/1.37  
% 2.73/1.37  %Foreground sorts:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Background operators:
% 2.73/1.37  
% 2.73/1.37  
% 2.73/1.37  %Foreground operators:
% 2.73/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.37  
% 2.73/1.39  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.73/1.39  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.39  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.39  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.73/1.39  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.39  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.73/1.39  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.39  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.73/1.39  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.73/1.39  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.73/1.39  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.39  tff(c_32, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.73/1.39  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.73/1.39  tff(c_62, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.73/1.39  tff(c_68, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.73/1.39  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_68])).
% 2.73/1.39  tff(c_18, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | k2_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.39  tff(c_76, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_18])).
% 2.73/1.39  tff(c_77, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 2.73/1.39  tff(c_78, plain, (![A_48]: (k2_relat_1(A_48)=k1_xboole_0 | k1_relat_1(A_48)!=k1_xboole_0 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.39  tff(c_81, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_78])).
% 2.73/1.39  tff(c_87, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_77, c_81])).
% 2.73/1.39  tff(c_128, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.73/1.39  tff(c_137, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_128])).
% 2.73/1.39  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.39  tff(c_265, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.39  tff(c_279, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_265])).
% 2.73/1.39  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.39  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.39  tff(c_149, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.39  tff(c_157, plain, (![A_71, B_72, A_73]: (m1_subset_1(A_71, B_72) | ~r2_hidden(A_71, A_73) | ~r1_tarski(A_73, B_72))), inference(resolution, [status(thm)], [c_6, c_149])).
% 2.73/1.39  tff(c_161, plain, (![A_74, B_75]: (m1_subset_1('#skF_1'(A_74), B_75) | ~r1_tarski(A_74, B_75) | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_2, c_157])).
% 2.73/1.39  tff(c_51, plain, (![D_44]: (~r2_hidden(D_44, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_44, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.73/1.39  tff(c_56, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_51])).
% 2.73/1.39  tff(c_97, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 2.73/1.39  tff(c_187, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_97])).
% 2.73/1.39  tff(c_231, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_187])).
% 2.73/1.39  tff(c_280, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_231])).
% 2.73/1.39  tff(c_289, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_280])).
% 2.73/1.39  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_137, c_289])).
% 2.73/1.39  tff(c_294, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 2.73/1.39  tff(c_351, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.39  tff(c_362, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_351])).
% 2.73/1.39  tff(c_366, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_294, c_362])).
% 2.73/1.39  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_366])).
% 2.73/1.39  tff(c_369, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.73/1.39  tff(c_512, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.39  tff(c_523, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_512])).
% 2.73/1.39  tff(c_527, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_369, c_523])).
% 2.73/1.39  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_527])).
% 2.73/1.39  tff(c_531, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_76])).
% 2.73/1.39  tff(c_718, plain, (![A_185, B_186, C_187]: (k2_relset_1(A_185, B_186, C_187)=k2_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.39  tff(c_729, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_718])).
% 2.73/1.39  tff(c_733, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_531, c_729])).
% 2.73/1.39  tff(c_735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_733])).
% 2.73/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.39  
% 2.73/1.39  Inference rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Ref     : 0
% 2.73/1.39  #Sup     : 139
% 2.73/1.39  #Fact    : 0
% 2.73/1.39  #Define  : 0
% 2.73/1.39  #Split   : 7
% 2.73/1.39  #Chain   : 0
% 2.73/1.39  #Close   : 0
% 2.73/1.39  
% 2.73/1.39  Ordering : KBO
% 2.73/1.39  
% 2.73/1.39  Simplification rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Subsume      : 5
% 2.73/1.39  #Demod        : 38
% 2.73/1.39  #Tautology    : 42
% 2.73/1.39  #SimpNegUnit  : 4
% 2.73/1.39  #BackRed      : 8
% 2.73/1.39  
% 2.73/1.39  #Partial instantiations: 0
% 2.73/1.39  #Strategies tried      : 1
% 2.73/1.39  
% 2.73/1.39  Timing (in seconds)
% 2.73/1.39  ----------------------
% 2.73/1.39  Preprocessing        : 0.30
% 2.73/1.39  Parsing              : 0.16
% 2.73/1.39  CNF conversion       : 0.02
% 2.73/1.39  Main loop            : 0.32
% 2.73/1.39  Inferencing          : 0.13
% 2.73/1.39  Reduction            : 0.09
% 2.73/1.39  Demodulation         : 0.06
% 2.73/1.39  BG Simplification    : 0.02
% 2.73/1.39  Subsumption          : 0.04
% 2.73/1.39  Abstraction          : 0.02
% 2.73/1.39  MUC search           : 0.00
% 2.73/1.39  Cooper               : 0.00
% 2.73/1.39  Total                : 0.66
% 2.73/1.39  Index Insertion      : 0.00
% 2.73/1.39  Index Deletion       : 0.00
% 2.73/1.39  Index Matching       : 0.00
% 2.73/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
