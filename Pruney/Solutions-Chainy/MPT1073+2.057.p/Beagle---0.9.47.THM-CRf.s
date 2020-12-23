%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   50 (  80 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 209 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
          & ! [E] :
              ~ ( r2_hidden(E,A)
                & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_20,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [B_18,A_19] :
      ( m1_subset_1(B_18,A_19)
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [E_13] :
      ( k1_funct_1('#skF_6',E_13) != '#skF_3'
      | ~ m1_subset_1(E_13,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43,plain,(
    ! [B_18] :
      ( k1_funct_1('#skF_6',B_18) != '#skF_3'
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_18])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    ! [A_27,B_28,C_29,D_30] :
      ( r2_hidden('#skF_2'(A_27,B_28,C_29,D_30),A_27)
      | ~ r2_hidden(C_29,k2_relset_1(A_27,B_28,D_30))
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(D_30,A_27,B_28)
      | ~ v1_funct_1(D_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    ! [C_29] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_29,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_29,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_91])).

tff(c_105,plain,(
    ! [C_31] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_31,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_31,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_99])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [C_31] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_31,'#skF_6'),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(C_31,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_105,c_6])).

tff(c_116,plain,(
    ! [C_32] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5',C_32,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_32,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_108])).

tff(c_131,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_142,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_18])).

tff(c_151,plain,(
    ! [D_33,A_34,B_35,C_36] :
      ( k1_funct_1(D_33,'#skF_2'(A_34,B_35,C_36,D_33)) = C_36
      | ~ r2_hidden(C_36,k2_relset_1(A_34,B_35,D_33))
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(D_33,A_34,B_35)
      | ~ v1_funct_1(D_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_156,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6')) = '#skF_3'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_151])).

tff(c_163,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_4','#skF_5','#skF_3','#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_156])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_163])).

tff(c_167,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_218,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( r2_hidden('#skF_2'(A_45,B_46,C_47,D_48),A_45)
      | ~ r2_hidden(C_47,k2_relset_1(A_45,B_46,D_48))
      | ~ m1_subset_1(D_48,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(D_48,A_45,B_46)
      | ~ v1_funct_1(D_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_226,plain,(
    ! [C_47] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_47,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_47,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_22,c_218])).

tff(c_232,plain,(
    ! [C_49] :
      ( r2_hidden('#skF_2'('#skF_4','#skF_5',C_49,'#skF_6'),'#skF_4')
      | ~ r2_hidden(C_49,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_226])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_238,plain,(
    ! [C_49] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(C_49,k2_relset_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_232,c_2])).

tff(c_243,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_238])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:25:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 1.96/1.29  
% 1.96/1.29  %Foreground sorts:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Background operators:
% 1.96/1.29  
% 1.96/1.29  
% 1.96/1.29  %Foreground operators:
% 1.96/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.96/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.96/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.96/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.96/1.29  tff('#skF_6', type, '#skF_6': $i).
% 1.96/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.29  
% 1.96/1.31  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 1.96/1.31  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.96/1.31  tff(f_59, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 1.96/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.96/1.31  tff(c_20, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.96/1.31  tff(c_38, plain, (![B_18, A_19]: (m1_subset_1(B_18, A_19) | ~v1_xboole_0(B_18) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.96/1.31  tff(c_18, plain, (![E_13]: (k1_funct_1('#skF_6', E_13)!='#skF_3' | ~m1_subset_1(E_13, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.96/1.31  tff(c_43, plain, (![B_18]: (k1_funct_1('#skF_6', B_18)!='#skF_3' | ~v1_xboole_0(B_18) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_18])).
% 1.96/1.31  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_43])).
% 1.96/1.31  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.96/1.31  tff(c_24, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.96/1.31  tff(c_22, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.96/1.31  tff(c_91, plain, (![A_27, B_28, C_29, D_30]: (r2_hidden('#skF_2'(A_27, B_28, C_29, D_30), A_27) | ~r2_hidden(C_29, k2_relset_1(A_27, B_28, D_30)) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(D_30, A_27, B_28) | ~v1_funct_1(D_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.31  tff(c_99, plain, (![C_29]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_29, '#skF_6'), '#skF_4') | ~r2_hidden(C_29, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_22, c_91])).
% 1.96/1.31  tff(c_105, plain, (![C_31]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_31, '#skF_6'), '#skF_4') | ~r2_hidden(C_31, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_99])).
% 1.96/1.31  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.96/1.31  tff(c_108, plain, (![C_31]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_31, '#skF_6'), '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden(C_31, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_105, c_6])).
% 1.96/1.31  tff(c_116, plain, (![C_32]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', C_32, '#skF_6'), '#skF_4') | ~r2_hidden(C_32, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_44, c_108])).
% 1.96/1.31  tff(c_131, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_116])).
% 1.96/1.31  tff(c_142, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_131, c_18])).
% 1.96/1.31  tff(c_151, plain, (![D_33, A_34, B_35, C_36]: (k1_funct_1(D_33, '#skF_2'(A_34, B_35, C_36, D_33))=C_36 | ~r2_hidden(C_36, k2_relset_1(A_34, B_35, D_33)) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(D_33, A_34, B_35) | ~v1_funct_1(D_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.31  tff(c_156, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'))='#skF_3' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_151])).
% 1.96/1.31  tff(c_163, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_3', '#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_156])).
% 1.96/1.31  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_163])).
% 1.96/1.31  tff(c_167, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_43])).
% 1.96/1.31  tff(c_218, plain, (![A_45, B_46, C_47, D_48]: (r2_hidden('#skF_2'(A_45, B_46, C_47, D_48), A_45) | ~r2_hidden(C_47, k2_relset_1(A_45, B_46, D_48)) | ~m1_subset_1(D_48, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(D_48, A_45, B_46) | ~v1_funct_1(D_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.31  tff(c_226, plain, (![C_47]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_47, '#skF_6'), '#skF_4') | ~r2_hidden(C_47, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_22, c_218])).
% 1.96/1.31  tff(c_232, plain, (![C_49]: (r2_hidden('#skF_2'('#skF_4', '#skF_5', C_49, '#skF_6'), '#skF_4') | ~r2_hidden(C_49, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_226])).
% 1.96/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.31  tff(c_238, plain, (![C_49]: (~v1_xboole_0('#skF_4') | ~r2_hidden(C_49, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_232, c_2])).
% 1.96/1.31  tff(c_243, plain, (![C_49]: (~r2_hidden(C_49, k2_relset_1('#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_238])).
% 1.96/1.31  tff(c_245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_20])).
% 1.96/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.31  
% 1.96/1.31  Inference rules
% 1.96/1.31  ----------------------
% 1.96/1.31  #Ref     : 0
% 1.96/1.31  #Sup     : 42
% 1.96/1.31  #Fact    : 0
% 1.96/1.31  #Define  : 0
% 1.96/1.31  #Split   : 3
% 1.96/1.31  #Chain   : 0
% 1.96/1.31  #Close   : 0
% 1.96/1.31  
% 1.96/1.31  Ordering : KBO
% 1.96/1.31  
% 1.96/1.31  Simplification rules
% 1.96/1.31  ----------------------
% 1.96/1.31  #Subsume      : 6
% 1.96/1.31  #Demod        : 10
% 1.96/1.31  #Tautology    : 11
% 1.96/1.31  #SimpNegUnit  : 8
% 1.96/1.31  #BackRed      : 1
% 1.96/1.31  
% 1.96/1.31  #Partial instantiations: 0
% 1.96/1.31  #Strategies tried      : 1
% 1.96/1.31  
% 1.96/1.31  Timing (in seconds)
% 1.96/1.31  ----------------------
% 1.96/1.31  Preprocessing        : 0.30
% 1.96/1.31  Parsing              : 0.16
% 1.96/1.31  CNF conversion       : 0.02
% 1.96/1.31  Main loop            : 0.20
% 1.96/1.31  Inferencing          : 0.08
% 1.96/1.31  Reduction            : 0.06
% 1.96/1.31  Demodulation         : 0.04
% 1.96/1.31  BG Simplification    : 0.01
% 1.96/1.31  Subsumption          : 0.03
% 1.96/1.31  Abstraction          : 0.01
% 1.96/1.31  MUC search           : 0.00
% 1.96/1.31  Cooper               : 0.00
% 1.96/1.31  Total                : 0.53
% 1.96/1.31  Index Insertion      : 0.00
% 1.96/1.31  Index Deletion       : 0.00
% 1.96/1.31  Index Matching       : 0.00
% 1.96/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
