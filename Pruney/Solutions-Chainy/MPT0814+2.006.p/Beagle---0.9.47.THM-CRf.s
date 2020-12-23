%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:51 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   53 (  99 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 217 expanded)
%              Number of equality atoms :   10 (  23 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_22,plain,(
    r2_hidden('#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_25,plain,(
    ! [B_26,A_27] :
      ( ~ r2_hidden(B_26,A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_25])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_46,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_43])).

tff(c_58,plain,(
    ! [A_36,C_37,B_38] :
      ( m1_subset_1(A_36,C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_61,plain,(
    ! [A_36] :
      ( m1_subset_1(A_36,k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_36,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( k4_tarski('#skF_2'(A_5,B_6,C_7),'#skF_3'(A_5,B_6,C_7)) = A_5
      | ~ r2_hidden(A_5,k2_zfmisc_1(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r2_hidden(A_44,C_45)
      | ~ r2_hidden(k4_tarski(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,(
    ! [A_72,C_73,D_74,B_75] :
      ( r2_hidden(A_72,C_73)
      | v1_xboole_0(k2_zfmisc_1(C_73,D_74))
      | ~ m1_subset_1(k4_tarski(A_72,B_75),k2_zfmisc_1(C_73,D_74)) ) ),
    inference(resolution,[status(thm)],[c_16,c_68])).

tff(c_153,plain,(
    ! [A_72,B_75] :
      ( r2_hidden(A_72,'#skF_5')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_72,B_75),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_61,c_146])).

tff(c_157,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(A_76,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_76,B_77),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_153])).

tff(c_160,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_2'(A_5,B_6,C_7),'#skF_5')
      | ~ r2_hidden(A_5,'#skF_7')
      | ~ r2_hidden(A_5,k2_zfmisc_1(B_6,C_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_157])).

tff(c_116,plain,(
    ! [A_67,B_68,C_69] :
      ( k4_tarski('#skF_2'(A_67,B_68,C_69),'#skF_3'(A_67,B_68,C_69)) = A_67
      | ~ r2_hidden(A_67,k2_zfmisc_1(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [B_40,D_41,A_42,C_43] :
      ( r2_hidden(B_40,D_41)
      | ~ r2_hidden(k4_tarski(A_42,B_40),k2_zfmisc_1(C_43,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [B_61,D_62,C_63,A_64] :
      ( r2_hidden(B_61,D_62)
      | v1_xboole_0(k2_zfmisc_1(C_63,D_62))
      | ~ m1_subset_1(k4_tarski(A_64,B_61),k2_zfmisc_1(C_63,D_62)) ) ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_105,plain,(
    ! [B_61,A_64] :
      ( r2_hidden(B_61,'#skF_6')
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_64,B_61),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_61,c_101])).

tff(c_108,plain,(
    ! [B_61,A_64] :
      ( r2_hidden(B_61,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_64,B_61),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_105])).

tff(c_180,plain,(
    ! [A_83,B_84,C_85] :
      ( r2_hidden('#skF_3'(A_83,B_84,C_85),'#skF_6')
      | ~ r2_hidden(A_83,'#skF_7')
      | ~ r2_hidden(A_83,k2_zfmisc_1(B_84,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_108])).

tff(c_20,plain,(
    ! [F_25,E_24] :
      ( ~ r2_hidden(F_25,'#skF_6')
      | ~ r2_hidden(E_24,'#skF_5')
      | k4_tarski(E_24,F_25) != '#skF_4' ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_217,plain,(
    ! [E_97,A_98,B_99,C_100] :
      ( ~ r2_hidden(E_97,'#skF_5')
      | k4_tarski(E_97,'#skF_3'(A_98,B_99,C_100)) != '#skF_4'
      | ~ r2_hidden(A_98,'#skF_7')
      | ~ r2_hidden(A_98,k2_zfmisc_1(B_99,C_100)) ) ),
    inference(resolution,[status(thm)],[c_180,c_20])).

tff(c_295,plain,(
    ! [A_133,B_134,C_135] :
      ( ~ r2_hidden('#skF_2'(A_133,B_134,C_135),'#skF_5')
      | A_133 != '#skF_4'
      | ~ r2_hidden(A_133,'#skF_7')
      | ~ r2_hidden(A_133,k2_zfmisc_1(B_134,C_135))
      | ~ r2_hidden(A_133,k2_zfmisc_1(B_134,C_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_217])).

tff(c_311,plain,(
    ! [A_136,B_137,C_138] :
      ( A_136 != '#skF_4'
      | ~ r2_hidden(A_136,'#skF_7')
      | ~ r2_hidden(A_136,k2_zfmisc_1(B_137,C_138)) ) ),
    inference(resolution,[status(thm)],[c_160,c_295])).

tff(c_327,plain,(
    ! [A_139,B_140,C_141] :
      ( A_139 != '#skF_4'
      | ~ r2_hidden(A_139,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1(B_140,C_141))
      | ~ m1_subset_1(A_139,k2_zfmisc_1(B_140,C_141)) ) ),
    inference(resolution,[status(thm)],[c_16,c_311])).

tff(c_330,plain,(
    ! [A_36] :
      ( A_36 != '#skF_4'
      | v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(A_36,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_61,c_327])).

tff(c_334,plain,(
    ~ r2_hidden('#skF_4','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_330])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.26  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.30/1.26  
% 2.30/1.26  %Foreground sorts:
% 2.30/1.26  
% 2.30/1.26  
% 2.30/1.26  %Background operators:
% 2.30/1.26  
% 2.30/1.26  
% 2.30/1.26  %Foreground operators:
% 2.30/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.30/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.30/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.30/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.30/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.26  
% 2.30/1.27  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.30/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.30/1.27  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.30/1.27  tff(f_63, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.30/1.27  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.30/1.27  tff(f_38, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.30/1.27  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.30/1.27  tff(c_22, plain, (r2_hidden('#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.30/1.27  tff(c_25, plain, (![B_26, A_27]: (~r2_hidden(B_26, A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.27  tff(c_29, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_22, c_25])).
% 2.30/1.27  tff(c_24, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.30/1.27  tff(c_40, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.30/1.27  tff(c_43, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.30/1.27  tff(c_46, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_29, c_43])).
% 2.30/1.27  tff(c_58, plain, (![A_36, C_37, B_38]: (m1_subset_1(A_36, C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.30/1.27  tff(c_61, plain, (![A_36]: (m1_subset_1(A_36, k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_36, '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_58])).
% 2.30/1.27  tff(c_16, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | v1_xboole_0(B_18) | ~m1_subset_1(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.27  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_tarski('#skF_2'(A_5, B_6, C_7), '#skF_3'(A_5, B_6, C_7))=A_5 | ~r2_hidden(A_5, k2_zfmisc_1(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.27  tff(c_68, plain, (![A_44, C_45, B_46, D_47]: (r2_hidden(A_44, C_45) | ~r2_hidden(k4_tarski(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.27  tff(c_146, plain, (![A_72, C_73, D_74, B_75]: (r2_hidden(A_72, C_73) | v1_xboole_0(k2_zfmisc_1(C_73, D_74)) | ~m1_subset_1(k4_tarski(A_72, B_75), k2_zfmisc_1(C_73, D_74)))), inference(resolution, [status(thm)], [c_16, c_68])).
% 2.30/1.27  tff(c_153, plain, (![A_72, B_75]: (r2_hidden(A_72, '#skF_5') | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(A_72, B_75), '#skF_7'))), inference(resolution, [status(thm)], [c_61, c_146])).
% 2.30/1.27  tff(c_157, plain, (![A_76, B_77]: (r2_hidden(A_76, '#skF_5') | ~r2_hidden(k4_tarski(A_76, B_77), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46, c_153])).
% 2.30/1.27  tff(c_160, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_2'(A_5, B_6, C_7), '#skF_5') | ~r2_hidden(A_5, '#skF_7') | ~r2_hidden(A_5, k2_zfmisc_1(B_6, C_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_157])).
% 2.30/1.27  tff(c_116, plain, (![A_67, B_68, C_69]: (k4_tarski('#skF_2'(A_67, B_68, C_69), '#skF_3'(A_67, B_68, C_69))=A_67 | ~r2_hidden(A_67, k2_zfmisc_1(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.27  tff(c_63, plain, (![B_40, D_41, A_42, C_43]: (r2_hidden(B_40, D_41) | ~r2_hidden(k4_tarski(A_42, B_40), k2_zfmisc_1(C_43, D_41)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.27  tff(c_101, plain, (![B_61, D_62, C_63, A_64]: (r2_hidden(B_61, D_62) | v1_xboole_0(k2_zfmisc_1(C_63, D_62)) | ~m1_subset_1(k4_tarski(A_64, B_61), k2_zfmisc_1(C_63, D_62)))), inference(resolution, [status(thm)], [c_16, c_63])).
% 2.30/1.27  tff(c_105, plain, (![B_61, A_64]: (r2_hidden(B_61, '#skF_6') | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(k4_tarski(A_64, B_61), '#skF_7'))), inference(resolution, [status(thm)], [c_61, c_101])).
% 2.30/1.27  tff(c_108, plain, (![B_61, A_64]: (r2_hidden(B_61, '#skF_6') | ~r2_hidden(k4_tarski(A_64, B_61), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_46, c_105])).
% 2.30/1.27  tff(c_180, plain, (![A_83, B_84, C_85]: (r2_hidden('#skF_3'(A_83, B_84, C_85), '#skF_6') | ~r2_hidden(A_83, '#skF_7') | ~r2_hidden(A_83, k2_zfmisc_1(B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_108])).
% 2.30/1.27  tff(c_20, plain, (![F_25, E_24]: (~r2_hidden(F_25, '#skF_6') | ~r2_hidden(E_24, '#skF_5') | k4_tarski(E_24, F_25)!='#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.30/1.27  tff(c_217, plain, (![E_97, A_98, B_99, C_100]: (~r2_hidden(E_97, '#skF_5') | k4_tarski(E_97, '#skF_3'(A_98, B_99, C_100))!='#skF_4' | ~r2_hidden(A_98, '#skF_7') | ~r2_hidden(A_98, k2_zfmisc_1(B_99, C_100)))), inference(resolution, [status(thm)], [c_180, c_20])).
% 2.30/1.27  tff(c_295, plain, (![A_133, B_134, C_135]: (~r2_hidden('#skF_2'(A_133, B_134, C_135), '#skF_5') | A_133!='#skF_4' | ~r2_hidden(A_133, '#skF_7') | ~r2_hidden(A_133, k2_zfmisc_1(B_134, C_135)) | ~r2_hidden(A_133, k2_zfmisc_1(B_134, C_135)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_217])).
% 2.30/1.27  tff(c_311, plain, (![A_136, B_137, C_138]: (A_136!='#skF_4' | ~r2_hidden(A_136, '#skF_7') | ~r2_hidden(A_136, k2_zfmisc_1(B_137, C_138)))), inference(resolution, [status(thm)], [c_160, c_295])).
% 2.30/1.27  tff(c_327, plain, (![A_139, B_140, C_141]: (A_139!='#skF_4' | ~r2_hidden(A_139, '#skF_7') | v1_xboole_0(k2_zfmisc_1(B_140, C_141)) | ~m1_subset_1(A_139, k2_zfmisc_1(B_140, C_141)))), inference(resolution, [status(thm)], [c_16, c_311])).
% 2.30/1.27  tff(c_330, plain, (![A_36]: (A_36!='#skF_4' | v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(A_36, '#skF_7'))), inference(resolution, [status(thm)], [c_61, c_327])).
% 2.30/1.27  tff(c_334, plain, (~r2_hidden('#skF_4', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_330])).
% 2.30/1.27  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_22])).
% 2.30/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  Inference rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Ref     : 0
% 2.30/1.27  #Sup     : 67
% 2.30/1.27  #Fact    : 0
% 2.30/1.27  #Define  : 0
% 2.30/1.27  #Split   : 6
% 2.30/1.27  #Chain   : 0
% 2.30/1.27  #Close   : 0
% 2.30/1.27  
% 2.30/1.27  Ordering : KBO
% 2.30/1.27  
% 2.30/1.27  Simplification rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Subsume      : 7
% 2.30/1.27  #Demod        : 0
% 2.30/1.27  #Tautology    : 6
% 2.30/1.27  #SimpNegUnit  : 8
% 2.30/1.27  #BackRed      : 1
% 2.30/1.27  
% 2.30/1.27  #Partial instantiations: 0
% 2.30/1.27  #Strategies tried      : 1
% 2.30/1.27  
% 2.30/1.27  Timing (in seconds)
% 2.30/1.27  ----------------------
% 2.30/1.27  Preprocessing        : 0.30
% 2.30/1.27  Parsing              : 0.17
% 2.30/1.27  CNF conversion       : 0.02
% 2.30/1.27  Main loop            : 0.28
% 2.30/1.27  Inferencing          : 0.12
% 2.30/1.27  Reduction            : 0.06
% 2.30/1.27  Demodulation         : 0.04
% 2.30/1.27  BG Simplification    : 0.01
% 2.30/1.27  Subsumption          : 0.06
% 2.30/1.27  Abstraction          : 0.01
% 2.30/1.27  MUC search           : 0.00
% 2.30/1.27  Cooper               : 0.00
% 2.30/1.28  Total                : 0.61
% 2.30/1.28  Index Insertion      : 0.00
% 2.30/1.28  Index Deletion       : 0.00
% 2.30/1.28  Index Matching       : 0.00
% 2.30/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
