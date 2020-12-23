%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:53 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  92 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 206 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [C_24,B_25,A_26] :
      ( ~ v1_xboole_0(C_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_26,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_22])).

tff(c_26,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_25])).

tff(c_32,plain,(
    ! [A_31,C_32,B_33] :
      ( m1_subset_1(A_31,C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_32])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_61,B_62,C_63] :
      ( k4_tarski('#skF_1'(A_61,B_62,C_63),'#skF_2'(A_61,B_62,C_63)) = A_61
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_27,C_28,B_29,D_30] :
      ( r2_hidden(A_27,C_28)
      | ~ r2_hidden(k4_tarski(A_27,B_29),k2_zfmisc_1(C_28,D_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ! [A_49,C_50,D_51,B_52] :
      ( r2_hidden(A_49,C_50)
      | v1_xboole_0(k2_zfmisc_1(C_50,D_51))
      | ~ m1_subset_1(k4_tarski(A_49,B_52),k2_zfmisc_1(C_50,D_51)) ) ),
    inference(resolution,[status(thm)],[c_10,c_27])).

tff(c_68,plain,(
    ! [A_49,B_52] :
      ( r2_hidden(A_49,'#skF_4')
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_49,B_52),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_35,c_64])).

tff(c_71,plain,(
    ! [A_49,B_52] :
      ( r2_hidden(A_49,'#skF_4')
      | ~ r2_hidden(k4_tarski(A_49,B_52),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_68])).

tff(c_104,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_1'(A_61,B_62,C_63),'#skF_4')
      | ~ r2_hidden(A_61,'#skF_6')
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_62,C_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_71])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [B_37,D_38,A_39,C_40] :
      ( r2_hidden(B_37,D_38)
      | ~ r2_hidden(k4_tarski(A_39,B_37),k2_zfmisc_1(C_40,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [B_55,D_56,C_57,A_58] :
      ( r2_hidden(B_55,D_56)
      | v1_xboole_0(k2_zfmisc_1(C_57,D_56))
      | ~ m1_subset_1(k4_tarski(A_58,B_55),k2_zfmisc_1(C_57,D_56)) ) ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_82,plain,(
    ! [B_55,A_58] :
      ( r2_hidden(B_55,'#skF_5')
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(k4_tarski(A_58,B_55),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_35,c_78])).

tff(c_85,plain,(
    ! [B_55,A_58] :
      ( r2_hidden(B_55,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_58,B_55),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_82])).

tff(c_124,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_2'(A_64,B_65,C_66),'#skF_5')
      | ~ r2_hidden(A_64,'#skF_6')
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_65,C_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_85])).

tff(c_16,plain,(
    ! [F_21,E_20] :
      ( ~ r2_hidden(F_21,'#skF_5')
      | ~ r2_hidden(E_20,'#skF_4')
      | k4_tarski(E_20,F_21) != '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_148,plain,(
    ! [E_80,A_81,B_82,C_83] :
      ( ~ r2_hidden(E_80,'#skF_4')
      | k4_tarski(E_80,'#skF_2'(A_81,B_82,C_83)) != '#skF_3'
      | ~ r2_hidden(A_81,'#skF_6')
      | ~ r2_hidden(A_81,k2_zfmisc_1(B_82,C_83)) ) ),
    inference(resolution,[status(thm)],[c_124,c_16])).

tff(c_155,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r2_hidden('#skF_1'(A_88,B_89,C_90),'#skF_4')
      | A_88 != '#skF_3'
      | ~ r2_hidden(A_88,'#skF_6')
      | ~ r2_hidden(A_88,k2_zfmisc_1(B_89,C_90))
      | ~ r2_hidden(A_88,k2_zfmisc_1(B_89,C_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_148])).

tff(c_165,plain,(
    ! [A_91,B_92,C_93] :
      ( A_91 != '#skF_3'
      | ~ r2_hidden(A_91,'#skF_6')
      | ~ r2_hidden(A_91,k2_zfmisc_1(B_92,C_93)) ) ),
    inference(resolution,[status(thm)],[c_104,c_155])).

tff(c_176,plain,(
    ! [A_94,B_95,C_96] :
      ( A_94 != '#skF_3'
      | ~ r2_hidden(A_94,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1(B_95,C_96))
      | ~ m1_subset_1(A_94,k2_zfmisc_1(B_95,C_96)) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_179,plain,(
    ! [A_31] :
      ( A_31 != '#skF_3'
      | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_35,c_176])).

tff(c_183,plain,(
    ~ r2_hidden('#skF_3','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_179])).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_18])).

tff(c_186,plain,(
    ! [A_26] : ~ r2_hidden(A_26,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_25])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.26  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.09/1.26  
% 2.09/1.26  %Foreground sorts:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Background operators:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Foreground operators:
% 2.09/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.26  
% 2.13/1.27  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.13/1.27  tff(f_57, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.13/1.27  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.13/1.27  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.13/1.27  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.13/1.27  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.13/1.27  tff(c_20, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.27  tff(c_22, plain, (![C_24, B_25, A_26]: (~v1_xboole_0(C_24) | ~m1_subset_1(B_25, k1_zfmisc_1(C_24)) | ~r2_hidden(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.27  tff(c_25, plain, (![A_26]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_26, '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_22])).
% 2.13/1.27  tff(c_26, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_25])).
% 2.13/1.27  tff(c_32, plain, (![A_31, C_32, B_33]: (m1_subset_1(A_31, C_32) | ~m1_subset_1(B_33, k1_zfmisc_1(C_32)) | ~r2_hidden(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.27  tff(c_35, plain, (![A_31]: (m1_subset_1(A_31, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_31, '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_32])).
% 2.13/1.27  tff(c_10, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.27  tff(c_92, plain, (![A_61, B_62, C_63]: (k4_tarski('#skF_1'(A_61, B_62, C_63), '#skF_2'(A_61, B_62, C_63))=A_61 | ~r2_hidden(A_61, k2_zfmisc_1(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.27  tff(c_27, plain, (![A_27, C_28, B_29, D_30]: (r2_hidden(A_27, C_28) | ~r2_hidden(k4_tarski(A_27, B_29), k2_zfmisc_1(C_28, D_30)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.27  tff(c_64, plain, (![A_49, C_50, D_51, B_52]: (r2_hidden(A_49, C_50) | v1_xboole_0(k2_zfmisc_1(C_50, D_51)) | ~m1_subset_1(k4_tarski(A_49, B_52), k2_zfmisc_1(C_50, D_51)))), inference(resolution, [status(thm)], [c_10, c_27])).
% 2.13/1.27  tff(c_68, plain, (![A_49, B_52]: (r2_hidden(A_49, '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(k4_tarski(A_49, B_52), '#skF_6'))), inference(resolution, [status(thm)], [c_35, c_64])).
% 2.13/1.27  tff(c_71, plain, (![A_49, B_52]: (r2_hidden(A_49, '#skF_4') | ~r2_hidden(k4_tarski(A_49, B_52), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_26, c_68])).
% 2.13/1.27  tff(c_104, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_1'(A_61, B_62, C_63), '#skF_4') | ~r2_hidden(A_61, '#skF_6') | ~r2_hidden(A_61, k2_zfmisc_1(B_62, C_63)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_71])).
% 2.13/1.27  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.27  tff(c_42, plain, (![B_37, D_38, A_39, C_40]: (r2_hidden(B_37, D_38) | ~r2_hidden(k4_tarski(A_39, B_37), k2_zfmisc_1(C_40, D_38)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.27  tff(c_78, plain, (![B_55, D_56, C_57, A_58]: (r2_hidden(B_55, D_56) | v1_xboole_0(k2_zfmisc_1(C_57, D_56)) | ~m1_subset_1(k4_tarski(A_58, B_55), k2_zfmisc_1(C_57, D_56)))), inference(resolution, [status(thm)], [c_10, c_42])).
% 2.13/1.27  tff(c_82, plain, (![B_55, A_58]: (r2_hidden(B_55, '#skF_5') | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(k4_tarski(A_58, B_55), '#skF_6'))), inference(resolution, [status(thm)], [c_35, c_78])).
% 2.13/1.27  tff(c_85, plain, (![B_55, A_58]: (r2_hidden(B_55, '#skF_5') | ~r2_hidden(k4_tarski(A_58, B_55), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_26, c_82])).
% 2.13/1.27  tff(c_124, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_2'(A_64, B_65, C_66), '#skF_5') | ~r2_hidden(A_64, '#skF_6') | ~r2_hidden(A_64, k2_zfmisc_1(B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_85])).
% 2.13/1.27  tff(c_16, plain, (![F_21, E_20]: (~r2_hidden(F_21, '#skF_5') | ~r2_hidden(E_20, '#skF_4') | k4_tarski(E_20, F_21)!='#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.27  tff(c_148, plain, (![E_80, A_81, B_82, C_83]: (~r2_hidden(E_80, '#skF_4') | k4_tarski(E_80, '#skF_2'(A_81, B_82, C_83))!='#skF_3' | ~r2_hidden(A_81, '#skF_6') | ~r2_hidden(A_81, k2_zfmisc_1(B_82, C_83)))), inference(resolution, [status(thm)], [c_124, c_16])).
% 2.13/1.27  tff(c_155, plain, (![A_88, B_89, C_90]: (~r2_hidden('#skF_1'(A_88, B_89, C_90), '#skF_4') | A_88!='#skF_3' | ~r2_hidden(A_88, '#skF_6') | ~r2_hidden(A_88, k2_zfmisc_1(B_89, C_90)) | ~r2_hidden(A_88, k2_zfmisc_1(B_89, C_90)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_148])).
% 2.13/1.27  tff(c_165, plain, (![A_91, B_92, C_93]: (A_91!='#skF_3' | ~r2_hidden(A_91, '#skF_6') | ~r2_hidden(A_91, k2_zfmisc_1(B_92, C_93)))), inference(resolution, [status(thm)], [c_104, c_155])).
% 2.13/1.27  tff(c_176, plain, (![A_94, B_95, C_96]: (A_94!='#skF_3' | ~r2_hidden(A_94, '#skF_6') | v1_xboole_0(k2_zfmisc_1(B_95, C_96)) | ~m1_subset_1(A_94, k2_zfmisc_1(B_95, C_96)))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.13/1.27  tff(c_179, plain, (![A_31]: (A_31!='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_31, '#skF_6'))), inference(resolution, [status(thm)], [c_35, c_176])).
% 2.13/1.27  tff(c_183, plain, (~r2_hidden('#skF_3', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_26, c_179])).
% 2.13/1.27  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.27  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_18])).
% 2.13/1.27  tff(c_186, plain, (![A_26]: (~r2_hidden(A_26, '#skF_6'))), inference(splitRight, [status(thm)], [c_25])).
% 2.13/1.27  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_18])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 35
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 4
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 3
% 2.13/1.27  #Demod        : 1
% 2.13/1.27  #Tautology    : 5
% 2.13/1.27  #SimpNegUnit  : 5
% 2.13/1.27  #BackRed      : 2
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.27
% 2.13/1.27  Parsing              : 0.15
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.21
% 2.13/1.27  Inferencing          : 0.09
% 2.13/1.27  Reduction            : 0.05
% 2.13/1.27  Demodulation         : 0.03
% 2.13/1.27  BG Simplification    : 0.01
% 2.13/1.28  Subsumption          : 0.04
% 2.13/1.28  Abstraction          : 0.01
% 2.13/1.28  MUC search           : 0.00
% 2.13/1.28  Cooper               : 0.00
% 2.13/1.28  Total                : 0.51
% 2.13/1.28  Index Insertion      : 0.00
% 2.13/1.28  Index Deletion       : 0.00
% 2.13/1.28  Index Matching       : 0.00
% 2.13/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
