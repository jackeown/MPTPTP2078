%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 140 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 342 expanded)
%              Number of equality atoms :   40 ( 117 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_120,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_182,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_191,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_182])).

tff(c_48,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_192,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_48])).

tff(c_637,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_1'(A_131,B_132,C_133),B_132)
      | k2_relset_1(A_131,B_132,C_133) = B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_648,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_637])).

tff(c_654,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_648])).

tff(c_655,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_654])).

tff(c_58,plain,(
    ! [D_42] :
      ( r2_hidden('#skF_6'(D_42),'#skF_3')
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_118,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_127,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_460,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_475,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_460])).

tff(c_482,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_127,c_475])).

tff(c_483,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_108,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_117,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,(
    ! [D_42] :
      ( k1_funct_1('#skF_5','#skF_6'(D_42)) = D_42
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_373,plain,(
    ! [B_98,A_99] :
      ( r2_hidden(k4_tarski(B_98,k1_funct_1(A_99,B_98)),A_99)
      | ~ r2_hidden(B_98,k1_relat_1(A_99))
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_376,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_6'(D_42),D_42),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_42),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_373])).

tff(c_378,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_6'(D_42),D_42),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_42),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_54,c_376])).

tff(c_484,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_6'(D_42),D_42),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_42),'#skF_3')
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_378])).

tff(c_777,plain,(
    ! [E_149,A_150,B_151,C_152] :
      ( ~ r2_hidden(k4_tarski(E_149,'#skF_1'(A_150,B_151,C_152)),C_152)
      | k2_relset_1(A_150,B_151,C_152) = B_151
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_842,plain,(
    ! [A_158,B_159] :
      ( k2_relset_1(A_158,B_159,'#skF_5') = B_159
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_158,B_159,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_158,B_159,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_484,c_777])).

tff(c_1075,plain,(
    ! [A_187,B_188] :
      ( k2_relset_1(A_187,B_188,'#skF_5') = B_188
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ r2_hidden('#skF_1'(A_187,B_188,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_842])).

tff(c_1081,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1075])).

tff(c_1085,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_191,c_1081])).

tff(c_1087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_1085])).

tff(c_1088,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1104,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_8])).

tff(c_238,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1(k2_relset_1(A_87,B_88,C_89),k1_zfmisc_1(B_88))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_262,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_238])).

tff(c_268,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_262])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_268,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_285,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_283,c_2])).

tff(c_288,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_285])).

tff(c_1111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.70  
% 3.65/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.70  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 3.65/1.70  
% 3.65/1.70  %Foreground sorts:
% 3.65/1.70  
% 3.65/1.70  
% 3.65/1.70  %Background operators:
% 3.65/1.70  
% 3.65/1.70  
% 3.65/1.70  %Foreground operators:
% 3.65/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.65/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.65/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.65/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.65/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.65/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.65/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.65/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.65/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.65/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.65/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.65/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.65/1.70  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.65/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.70  
% 3.65/1.72  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.65/1.72  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.65/1.72  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 3.65/1.72  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.65/1.72  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.65/1.72  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.65/1.72  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.65/1.72  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.65/1.72  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.65/1.72  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.65/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.65/1.72  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.72  tff(c_182, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.65/1.72  tff(c_191, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_182])).
% 3.65/1.72  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.72  tff(c_192, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_48])).
% 3.65/1.72  tff(c_637, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_1'(A_131, B_132, C_133), B_132) | k2_relset_1(A_131, B_132, C_133)=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.65/1.72  tff(c_648, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_637])).
% 3.65/1.72  tff(c_654, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_648])).
% 3.65/1.72  tff(c_655, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_192, c_654])).
% 3.65/1.72  tff(c_58, plain, (![D_42]: (r2_hidden('#skF_6'(D_42), '#skF_3') | ~r2_hidden(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.72  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.72  tff(c_118, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.65/1.72  tff(c_127, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_118])).
% 3.65/1.72  tff(c_460, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.65/1.72  tff(c_475, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_460])).
% 3.65/1.72  tff(c_482, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_127, c_475])).
% 3.65/1.72  tff(c_483, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_482])).
% 3.65/1.72  tff(c_108, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.72  tff(c_117, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_108])).
% 3.65/1.72  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.72  tff(c_56, plain, (![D_42]: (k1_funct_1('#skF_5', '#skF_6'(D_42))=D_42 | ~r2_hidden(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.72  tff(c_373, plain, (![B_98, A_99]: (r2_hidden(k4_tarski(B_98, k1_funct_1(A_99, B_98)), A_99) | ~r2_hidden(B_98, k1_relat_1(A_99)) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.65/1.72  tff(c_376, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_6'(D_42), D_42), '#skF_5') | ~r2_hidden('#skF_6'(D_42), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_42, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_373])).
% 3.65/1.72  tff(c_378, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_6'(D_42), D_42), '#skF_5') | ~r2_hidden('#skF_6'(D_42), k1_relat_1('#skF_5')) | ~r2_hidden(D_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_54, c_376])).
% 3.65/1.72  tff(c_484, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_6'(D_42), D_42), '#skF_5') | ~r2_hidden('#skF_6'(D_42), '#skF_3') | ~r2_hidden(D_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_378])).
% 3.65/1.72  tff(c_777, plain, (![E_149, A_150, B_151, C_152]: (~r2_hidden(k4_tarski(E_149, '#skF_1'(A_150, B_151, C_152)), C_152) | k2_relset_1(A_150, B_151, C_152)=B_151 | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.65/1.72  tff(c_842, plain, (![A_158, B_159]: (k2_relset_1(A_158, B_159, '#skF_5')=B_159 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~r2_hidden('#skF_6'('#skF_1'(A_158, B_159, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_158, B_159, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_484, c_777])).
% 3.65/1.72  tff(c_1075, plain, (![A_187, B_188]: (k2_relset_1(A_187, B_188, '#skF_5')=B_188 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~r2_hidden('#skF_1'(A_187, B_188, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_842])).
% 3.65/1.72  tff(c_1081, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1075])).
% 3.65/1.72  tff(c_1085, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_655, c_191, c_1081])).
% 3.65/1.72  tff(c_1087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_1085])).
% 3.65/1.72  tff(c_1088, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_482])).
% 3.65/1.72  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.72  tff(c_1104, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_8])).
% 3.65/1.72  tff(c_238, plain, (![A_87, B_88, C_89]: (m1_subset_1(k2_relset_1(A_87, B_88, C_89), k1_zfmisc_1(B_88)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.65/1.72  tff(c_262, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_191, c_238])).
% 3.65/1.72  tff(c_268, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_262])).
% 3.65/1.72  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.72  tff(c_283, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_268, c_10])).
% 3.65/1.72  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.72  tff(c_285, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_283, c_2])).
% 3.65/1.72  tff(c_288, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_192, c_285])).
% 3.65/1.72  tff(c_1111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1104, c_288])).
% 3.65/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.72  
% 3.65/1.72  Inference rules
% 3.65/1.72  ----------------------
% 3.65/1.72  #Ref     : 0
% 3.65/1.72  #Sup     : 201
% 3.65/1.72  #Fact    : 0
% 3.65/1.72  #Define  : 0
% 3.65/1.72  #Split   : 3
% 3.65/1.72  #Chain   : 0
% 3.65/1.72  #Close   : 0
% 3.65/1.72  
% 3.65/1.72  Ordering : KBO
% 3.65/1.72  
% 3.65/1.72  Simplification rules
% 3.65/1.72  ----------------------
% 3.65/1.72  #Subsume      : 11
% 3.65/1.72  #Demod        : 144
% 3.65/1.72  #Tautology    : 87
% 3.65/1.72  #SimpNegUnit  : 7
% 3.65/1.72  #BackRed      : 23
% 3.65/1.72  
% 3.65/1.72  #Partial instantiations: 0
% 3.65/1.72  #Strategies tried      : 1
% 3.65/1.72  
% 3.65/1.72  Timing (in seconds)
% 3.65/1.72  ----------------------
% 3.65/1.72  Preprocessing        : 0.42
% 3.65/1.72  Parsing              : 0.21
% 3.65/1.72  CNF conversion       : 0.03
% 3.65/1.72  Main loop            : 0.46
% 3.65/1.72  Inferencing          : 0.16
% 3.65/1.72  Reduction            : 0.15
% 3.65/1.72  Demodulation         : 0.10
% 3.65/1.72  BG Simplification    : 0.03
% 3.65/1.72  Subsumption          : 0.09
% 3.65/1.72  Abstraction          : 0.03
% 3.65/1.72  MUC search           : 0.00
% 3.65/1.72  Cooper               : 0.00
% 3.65/1.72  Total                : 0.92
% 3.65/1.72  Index Insertion      : 0.00
% 3.65/1.72  Index Deletion       : 0.00
% 3.65/1.72  Index Matching       : 0.00
% 3.65/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
