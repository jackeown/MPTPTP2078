%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:29 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 125 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 338 expanded)
%              Number of equality atoms :   15 (  61 expanded)
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

tff(f_82,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_22,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_relset_1(A_13,B_14,C_15),k1_zfmisc_1(B_14))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [C_39,A_40,B_41] :
      ( r2_hidden(C_39,A_40)
      | ~ r2_hidden(C_39,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_118,plain,(
    ! [A_52,B_53,A_54] :
      ( r2_hidden('#skF_1'(A_52,B_53),A_54)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(A_54))
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_58,A_59] :
      ( ~ m1_subset_1(A_58,k1_zfmisc_1(A_59))
      | r1_tarski(A_58,A_59) ) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_166,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(k2_relset_1(A_64,B_65,C_66),B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_173,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_166])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,
    ( k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_173,c_8])).

tff(c_181,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_177])).

tff(c_26,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [D_23] :
      ( r2_hidden('#skF_5'(D_23),'#skF_2')
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [D_23] :
      ( k1_funct_1('#skF_4','#skF_5'(D_23)) = D_23
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_154,plain,(
    ! [D_60,C_61,A_62,B_63] :
      ( r2_hidden(k1_funct_1(D_60,C_61),k2_relset_1(A_62,B_63,D_60))
      | k1_xboole_0 = B_63
      | ~ r2_hidden(C_61,A_62)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2(D_60,A_62,B_63)
      | ~ v1_funct_1(D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,(
    ! [D_23,A_62,B_63] :
      ( r2_hidden(D_23,k2_relset_1(A_62,B_63,'#skF_4'))
      | k1_xboole_0 = B_63
      | ~ r2_hidden('#skF_5'(D_23),A_62)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2('#skF_4',A_62,B_63)
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(D_23,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_154])).

tff(c_191,plain,(
    ! [D_70,A_71,B_72] :
      ( r2_hidden(D_70,k2_relset_1(A_71,B_72,'#skF_4'))
      | k1_xboole_0 = B_72
      | ~ r2_hidden('#skF_5'(D_70),A_71)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2('#skF_4',A_71,B_72)
      | ~ r2_hidden(D_70,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_161])).

tff(c_215,plain,(
    ! [D_76,B_77] :
      ( r2_hidden(D_76,k2_relset_1('#skF_2',B_77,'#skF_4'))
      | k1_xboole_0 = B_77
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_77)))
      | ~ v1_funct_2('#skF_4','#skF_2',B_77)
      | ~ r2_hidden(D_76,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_191])).

tff(c_217,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ r2_hidden(D_76,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_215])).

tff(c_220,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(D_76,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_217])).

tff(c_221,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_228,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_14])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_181])).

tff(c_238,plain,(
    ! [D_78] :
      ( r2_hidden(D_78,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(D_78,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_420,plain,(
    ! [A_114] :
      ( r1_tarski(A_114,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden('#skF_1'(A_114,k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_238,c_4])).

tff(c_436,plain,(
    r1_tarski('#skF_3',k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_420])).

tff(c_443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_181,c_436])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.65/1.41  
% 2.65/1.41  %Foreground sorts:
% 2.65/1.41  
% 2.65/1.41  
% 2.65/1.41  %Background operators:
% 2.65/1.41  
% 2.65/1.41  
% 2.65/1.41  %Foreground operators:
% 2.65/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.41  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.65/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.41  
% 2.65/1.42  tff(f_82, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.65/1.42  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.65/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.65/1.42  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.65/1.42  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.42  tff(f_63, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.65/1.42  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.42  tff(c_22, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_18, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_relset_1(A_13, B_14, C_15), k1_zfmisc_1(B_14)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.42  tff(c_84, plain, (![C_39, A_40, B_41]: (r2_hidden(C_39, A_40) | ~r2_hidden(C_39, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.42  tff(c_118, plain, (![A_52, B_53, A_54]: (r2_hidden('#skF_1'(A_52, B_53), A_54) | ~m1_subset_1(A_52, k1_zfmisc_1(A_54)) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_6, c_84])).
% 2.65/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.42  tff(c_137, plain, (![A_58, A_59]: (~m1_subset_1(A_58, k1_zfmisc_1(A_59)) | r1_tarski(A_58, A_59))), inference(resolution, [status(thm)], [c_118, c_4])).
% 2.65/1.42  tff(c_166, plain, (![A_64, B_65, C_66]: (r1_tarski(k2_relset_1(A_64, B_65, C_66), B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(resolution, [status(thm)], [c_18, c_137])).
% 2.65/1.42  tff(c_173, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_24, c_166])).
% 2.65/1.42  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.65/1.42  tff(c_177, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_173, c_8])).
% 2.65/1.42  tff(c_181, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_22, c_177])).
% 2.65/1.42  tff(c_26, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_32, plain, (![D_23]: (r2_hidden('#skF_5'(D_23), '#skF_2') | ~r2_hidden(D_23, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_30, plain, (![D_23]: (k1_funct_1('#skF_4', '#skF_5'(D_23))=D_23 | ~r2_hidden(D_23, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.65/1.42  tff(c_154, plain, (![D_60, C_61, A_62, B_63]: (r2_hidden(k1_funct_1(D_60, C_61), k2_relset_1(A_62, B_63, D_60)) | k1_xboole_0=B_63 | ~r2_hidden(C_61, A_62) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2(D_60, A_62, B_63) | ~v1_funct_1(D_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.65/1.42  tff(c_161, plain, (![D_23, A_62, B_63]: (r2_hidden(D_23, k2_relset_1(A_62, B_63, '#skF_4')) | k1_xboole_0=B_63 | ~r2_hidden('#skF_5'(D_23), A_62) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2('#skF_4', A_62, B_63) | ~v1_funct_1('#skF_4') | ~r2_hidden(D_23, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_154])).
% 2.65/1.42  tff(c_191, plain, (![D_70, A_71, B_72]: (r2_hidden(D_70, k2_relset_1(A_71, B_72, '#skF_4')) | k1_xboole_0=B_72 | ~r2_hidden('#skF_5'(D_70), A_71) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2('#skF_4', A_71, B_72) | ~r2_hidden(D_70, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_161])).
% 2.65/1.42  tff(c_215, plain, (![D_76, B_77]: (r2_hidden(D_76, k2_relset_1('#skF_2', B_77, '#skF_4')) | k1_xboole_0=B_77 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_77))) | ~v1_funct_2('#skF_4', '#skF_2', B_77) | ~r2_hidden(D_76, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_191])).
% 2.65/1.42  tff(c_217, plain, (![D_76]: (r2_hidden(D_76, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~r2_hidden(D_76, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_215])).
% 2.65/1.42  tff(c_220, plain, (![D_76]: (r2_hidden(D_76, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_3' | ~r2_hidden(D_76, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_217])).
% 2.65/1.42  tff(c_221, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_220])).
% 2.65/1.42  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.42  tff(c_228, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_14])).
% 2.65/1.42  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_181])).
% 2.65/1.42  tff(c_238, plain, (![D_78]: (r2_hidden(D_78, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(D_78, '#skF_3'))), inference(splitRight, [status(thm)], [c_220])).
% 2.65/1.42  tff(c_420, plain, (![A_114]: (r1_tarski(A_114, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'(A_114, k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_238, c_4])).
% 2.65/1.42  tff(c_436, plain, (r1_tarski('#skF_3', k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_420])).
% 2.65/1.42  tff(c_443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_181, c_436])).
% 2.65/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.42  
% 2.65/1.42  Inference rules
% 2.65/1.42  ----------------------
% 2.65/1.42  #Ref     : 0
% 2.65/1.42  #Sup     : 94
% 2.65/1.42  #Fact    : 0
% 2.65/1.42  #Define  : 0
% 2.65/1.42  #Split   : 7
% 2.65/1.42  #Chain   : 0
% 2.65/1.42  #Close   : 0
% 2.65/1.42  
% 2.65/1.42  Ordering : KBO
% 2.65/1.42  
% 2.65/1.42  Simplification rules
% 2.65/1.42  ----------------------
% 2.65/1.42  #Subsume      : 13
% 2.65/1.42  #Demod        : 22
% 2.65/1.42  #Tautology    : 18
% 2.65/1.42  #SimpNegUnit  : 3
% 2.65/1.42  #BackRed      : 8
% 2.65/1.42  
% 2.65/1.42  #Partial instantiations: 0
% 2.65/1.42  #Strategies tried      : 1
% 2.65/1.42  
% 2.65/1.42  Timing (in seconds)
% 2.65/1.42  ----------------------
% 2.65/1.42  Preprocessing        : 0.32
% 2.65/1.42  Parsing              : 0.16
% 2.65/1.42  CNF conversion       : 0.03
% 2.65/1.42  Main loop            : 0.34
% 2.65/1.42  Inferencing          : 0.13
% 2.65/1.42  Reduction            : 0.09
% 2.65/1.42  Demodulation         : 0.06
% 2.65/1.42  BG Simplification    : 0.02
% 2.65/1.42  Subsumption          : 0.09
% 2.65/1.42  Abstraction          : 0.01
% 2.65/1.42  MUC search           : 0.00
% 2.65/1.42  Cooper               : 0.00
% 2.65/1.42  Total                : 0.69
% 2.65/1.42  Index Insertion      : 0.00
% 2.65/1.42  Index Deletion       : 0.00
% 2.65/1.42  Index Matching       : 0.00
% 2.65/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
