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
% DateTime   : Thu Dec  3 10:16:54 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 134 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  129 ( 448 expanded)
%              Number of equality atoms :   12 (  61 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_165,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_165])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_42,B_43,D_44] :
      ( r2_relset_1(A_42,B_43,D_44,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | ~ v1_xboole_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_41,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_75,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_79,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_96,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_partfun1(C_48,A_49)
      | ~ v1_funct_2(C_48,A_49,B_50)
      | ~ v1_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | v1_xboole_0(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_105,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_99])).

tff(c_106,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_105])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_102,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_109,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_102])).

tff(c_110,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_109])).

tff(c_32,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_128,plain,(
    ! [D_59,C_60,A_61,B_62] :
      ( D_59 = C_60
      | ~ r1_partfun1(C_60,D_59)
      | ~ v1_partfun1(D_59,A_61)
      | ~ v1_partfun1(C_60,A_61)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_1(D_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_130,plain,(
    ! [A_61,B_62] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_61)
      | ~ v1_partfun1('#skF_4',A_61)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_133,plain,(
    ! [A_61,B_62] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_61)
      | ~ v1_partfun1('#skF_4',A_61)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_130])).

tff(c_135,plain,(
    ! [A_63,B_64] :
      ( ~ v1_partfun1('#skF_5',A_63)
      | ~ v1_partfun1('#skF_4',A_63)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_63,B_64)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_106,c_110,c_138])).

tff(c_143,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_147,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_28])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_147])).

tff(c_158,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_74,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_41,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_191,plain,(
    ! [A_71] : ~ r2_hidden(A_71,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_74])).

tff(c_197,plain,(
    ! [B_72] : r1_tarski('#skF_5',B_72) ),
    inference(resolution,[status(thm)],[c_6,c_191])).

tff(c_159,plain,(
    ! [A_65] : ~ r2_hidden(A_65,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_172,plain,(
    ! [B_69] : r1_tarski('#skF_4',B_69) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_175,plain,(
    ! [B_69] :
      ( B_69 = '#skF_4'
      | ~ r1_tarski(B_69,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_172,c_8])).

tff(c_204,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_197,c_175])).

tff(c_210,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_28])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.02/1.32  
% 2.02/1.32  %Foreground sorts:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Background operators:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Foreground operators:
% 2.02/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.02/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.02/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.02/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.32  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.02/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.32  
% 2.30/1.34  tff(f_111, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.30/1.34  tff(f_57, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.30/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.30/1.34  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.30/1.34  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.30/1.34  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.30/1.34  tff(f_88, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.30/1.34  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.34  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_165, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.34  tff(c_170, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_165])).
% 2.30/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.30/1.34  tff(c_80, plain, (![A_42, B_43, D_44]: (r2_relset_1(A_42, B_43, D_44, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.34  tff(c_85, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_80])).
% 2.30/1.34  tff(c_14, plain, (![A_8, B_9]: (v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | ~v1_xboole_0(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.30/1.34  tff(c_68, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.30/1.34  tff(c_73, plain, (![A_41]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_41, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 2.30/1.34  tff(c_75, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_73])).
% 2.30/1.34  tff(c_79, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_75])).
% 2.30/1.34  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_96, plain, (![C_48, A_49, B_50]: (v1_partfun1(C_48, A_49) | ~v1_funct_2(C_48, A_49, B_50) | ~v1_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | v1_xboole_0(B_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.34  tff(c_99, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_96])).
% 2.30/1.34  tff(c_105, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_99])).
% 2.30/1.34  tff(c_106, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_79, c_105])).
% 2.30/1.34  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_102, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_96])).
% 2.30/1.34  tff(c_109, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_102])).
% 2.30/1.34  tff(c_110, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_79, c_109])).
% 2.30/1.34  tff(c_32, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_128, plain, (![D_59, C_60, A_61, B_62]: (D_59=C_60 | ~r1_partfun1(C_60, D_59) | ~v1_partfun1(D_59, A_61) | ~v1_partfun1(C_60, A_61) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_1(D_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_1(C_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.30/1.34  tff(c_130, plain, (![A_61, B_62]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_61) | ~v1_partfun1('#skF_4', A_61) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_128])).
% 2.30/1.34  tff(c_133, plain, (![A_61, B_62]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_61) | ~v1_partfun1('#skF_4', A_61) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_130])).
% 2.30/1.34  tff(c_135, plain, (![A_63, B_64]: (~v1_partfun1('#skF_5', A_63) | ~v1_partfun1('#skF_4', A_63) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(splitLeft, [status(thm)], [c_133])).
% 2.30/1.34  tff(c_138, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_34, c_135])).
% 2.30/1.34  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_106, c_110, c_138])).
% 2.30/1.34  tff(c_143, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_133])).
% 2.30/1.34  tff(c_28, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.34  tff(c_147, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_28])).
% 2.30/1.34  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_147])).
% 2.30/1.34  tff(c_158, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_73])).
% 2.30/1.34  tff(c_74, plain, (![A_41]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_41, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_68])).
% 2.30/1.34  tff(c_191, plain, (![A_71]: (~r2_hidden(A_71, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_74])).
% 2.30/1.34  tff(c_197, plain, (![B_72]: (r1_tarski('#skF_5', B_72))), inference(resolution, [status(thm)], [c_6, c_191])).
% 2.30/1.34  tff(c_159, plain, (![A_65]: (~r2_hidden(A_65, '#skF_4'))), inference(splitRight, [status(thm)], [c_73])).
% 2.30/1.34  tff(c_172, plain, (![B_69]: (r1_tarski('#skF_4', B_69))), inference(resolution, [status(thm)], [c_6, c_159])).
% 2.30/1.34  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.34  tff(c_175, plain, (![B_69]: (B_69='#skF_4' | ~r1_tarski(B_69, '#skF_4'))), inference(resolution, [status(thm)], [c_172, c_8])).
% 2.30/1.34  tff(c_204, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_197, c_175])).
% 2.30/1.34  tff(c_210, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_28])).
% 2.30/1.34  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_210])).
% 2.30/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.34  
% 2.30/1.34  Inference rules
% 2.30/1.34  ----------------------
% 2.30/1.34  #Ref     : 0
% 2.30/1.34  #Sup     : 26
% 2.30/1.34  #Fact    : 0
% 2.30/1.34  #Define  : 0
% 2.30/1.34  #Split   : 3
% 2.30/1.34  #Chain   : 0
% 2.30/1.34  #Close   : 0
% 2.30/1.34  
% 2.30/1.34  Ordering : KBO
% 2.30/1.34  
% 2.30/1.34  Simplification rules
% 2.30/1.34  ----------------------
% 2.30/1.34  #Subsume      : 3
% 2.30/1.34  #Demod        : 40
% 2.30/1.34  #Tautology    : 15
% 2.30/1.34  #SimpNegUnit  : 2
% 2.30/1.34  #BackRed      : 15
% 2.30/1.34  
% 2.30/1.34  #Partial instantiations: 0
% 2.30/1.34  #Strategies tried      : 1
% 2.30/1.34  
% 2.30/1.34  Timing (in seconds)
% 2.30/1.34  ----------------------
% 2.30/1.34  Preprocessing        : 0.33
% 2.30/1.34  Parsing              : 0.18
% 2.30/1.34  CNF conversion       : 0.02
% 2.30/1.34  Main loop            : 0.18
% 2.30/1.34  Inferencing          : 0.06
% 2.30/1.34  Reduction            : 0.05
% 2.30/1.34  Demodulation         : 0.04
% 2.30/1.34  BG Simplification    : 0.01
% 2.30/1.34  Subsumption          : 0.03
% 2.30/1.34  Abstraction          : 0.01
% 2.30/1.34  MUC search           : 0.00
% 2.30/1.34  Cooper               : 0.00
% 2.30/1.34  Total                : 0.54
% 2.30/1.34  Index Insertion      : 0.00
% 2.30/1.34  Index Deletion       : 0.00
% 2.30/1.34  Index Matching       : 0.00
% 2.30/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
