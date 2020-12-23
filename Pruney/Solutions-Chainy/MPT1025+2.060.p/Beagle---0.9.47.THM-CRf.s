%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 196 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
            & ! [F] :
                ~ ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_22,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_75,plain,(
    ! [C_46,A_47,D_49,E_45,B_48] :
      ( r2_hidden('#skF_2'(E_45,C_46,A_47,B_48,D_49),A_47)
      | ~ r2_hidden(E_45,k7_relset_1(A_47,B_48,D_49,C_46))
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_2(D_49,A_47,B_48)
      | ~ v1_funct_1(D_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    ! [E_45,C_46] :
      ( r2_hidden('#skF_2'(E_45,C_46,'#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ r2_hidden(E_45,k7_relset_1('#skF_3','#skF_4','#skF_6',C_46))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_242,plain,(
    ! [E_89,C_90] :
      ( r2_hidden('#skF_2'(E_89,C_90,'#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ r2_hidden(E_89,k7_relset_1('#skF_3','#skF_4','#skF_6',C_90)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_80])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_38,B_7,A_6] :
      ( m1_subset_1(A_38,B_7)
      | ~ r2_hidden(A_38,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_612,plain,(
    ! [E_137,C_138,B_139] :
      ( m1_subset_1('#skF_2'(E_137,C_138,'#skF_3','#skF_4','#skF_6'),B_139)
      | ~ r1_tarski('#skF_3',B_139)
      | ~ r2_hidden(E_137,k7_relset_1('#skF_3','#skF_4','#skF_6',C_138)) ) ),
    inference(resolution,[status(thm)],[c_242,c_65])).

tff(c_648,plain,(
    ! [B_140] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_3','#skF_4','#skF_6'),B_140)
      | ~ r1_tarski('#skF_3',B_140) ) ),
    inference(resolution,[status(thm)],[c_22,c_612])).

tff(c_208,plain,(
    ! [D_86,C_83,B_85,E_82,A_84] :
      ( k1_funct_1(D_86,'#skF_2'(E_82,C_83,A_84,B_85,D_86)) = E_82
      | ~ r2_hidden(E_82,k7_relset_1(A_84,B_85,D_86,C_83))
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_2(D_86,A_84,B_85)
      | ~ v1_funct_1(D_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_216,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_3','#skF_4','#skF_6')) = '#skF_7'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_208])).

tff(c_221,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_3','#skF_4','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_216])).

tff(c_137,plain,(
    ! [D_66,E_62,C_63,A_64,B_65] :
      ( r2_hidden('#skF_2'(E_62,C_63,A_64,B_65,D_66),C_63)
      | ~ r2_hidden(E_62,k7_relset_1(A_64,B_65,D_66,C_63))
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_2(D_66,A_64,B_65)
      | ~ v1_funct_1(D_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_145,plain,(
    ! [E_62,C_63] :
      ( r2_hidden('#skF_2'(E_62,C_63,'#skF_3','#skF_4','#skF_6'),C_63)
      | ~ r2_hidden(E_62,k7_relset_1('#skF_3','#skF_4','#skF_6',C_63))
      | ~ v1_funct_2('#skF_6','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_137])).

tff(c_226,plain,(
    ! [E_87,C_88] :
      ( r2_hidden('#skF_2'(E_87,C_88,'#skF_3','#skF_4','#skF_6'),C_88)
      | ~ r2_hidden(E_87,k7_relset_1('#skF_3','#skF_4','#skF_6',C_88)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_145])).

tff(c_20,plain,(
    ! [F_24] :
      ( k1_funct_1('#skF_6',F_24) != '#skF_7'
      | ~ r2_hidden(F_24,'#skF_5')
      | ~ m1_subset_1(F_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_249,plain,(
    ! [E_91] :
      ( k1_funct_1('#skF_6','#skF_2'(E_91,'#skF_5','#skF_3','#skF_4','#skF_6')) != '#skF_7'
      | ~ m1_subset_1('#skF_2'(E_91,'#skF_5','#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ r2_hidden(E_91,k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_226,c_20])).

tff(c_264,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_3','#skF_4','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_270,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_264])).

tff(c_651,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_648,c_270])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.42  
% 2.88/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.43  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k7_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.88/1.43  
% 2.88/1.43  %Foreground sorts:
% 2.88/1.43  
% 2.88/1.43  
% 2.88/1.43  %Background operators:
% 2.88/1.43  
% 2.88/1.43  
% 2.88/1.43  %Foreground operators:
% 2.88/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.88/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.88/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.43  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.88/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.88/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.43  
% 2.88/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.88/1.44  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.88/1.44  tff(f_60, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.88/1.44  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.88/1.44  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.88/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.44  tff(c_40, plain, (![A_31, B_32]: (~r2_hidden('#skF_1'(A_31, B_32), B_32) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.44  tff(c_45, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.88/1.44  tff(c_22, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.44  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.44  tff(c_26, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.44  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.44  tff(c_75, plain, (![C_46, A_47, D_49, E_45, B_48]: (r2_hidden('#skF_2'(E_45, C_46, A_47, B_48, D_49), A_47) | ~r2_hidden(E_45, k7_relset_1(A_47, B_48, D_49, C_46)) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_2(D_49, A_47, B_48) | ~v1_funct_1(D_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.44  tff(c_80, plain, (![E_45, C_46]: (r2_hidden('#skF_2'(E_45, C_46, '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~r2_hidden(E_45, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_46)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_75])).
% 2.88/1.44  tff(c_242, plain, (![E_89, C_90]: (r2_hidden('#skF_2'(E_89, C_90, '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~r2_hidden(E_89, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_90)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_80])).
% 2.88/1.44  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.88/1.44  tff(c_60, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.44  tff(c_65, plain, (![A_38, B_7, A_6]: (m1_subset_1(A_38, B_7) | ~r2_hidden(A_38, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.88/1.44  tff(c_612, plain, (![E_137, C_138, B_139]: (m1_subset_1('#skF_2'(E_137, C_138, '#skF_3', '#skF_4', '#skF_6'), B_139) | ~r1_tarski('#skF_3', B_139) | ~r2_hidden(E_137, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_138)))), inference(resolution, [status(thm)], [c_242, c_65])).
% 2.88/1.44  tff(c_648, plain, (![B_140]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_3', '#skF_4', '#skF_6'), B_140) | ~r1_tarski('#skF_3', B_140))), inference(resolution, [status(thm)], [c_22, c_612])).
% 2.88/1.44  tff(c_208, plain, (![D_86, C_83, B_85, E_82, A_84]: (k1_funct_1(D_86, '#skF_2'(E_82, C_83, A_84, B_85, D_86))=E_82 | ~r2_hidden(E_82, k7_relset_1(A_84, B_85, D_86, C_83)) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_2(D_86, A_84, B_85) | ~v1_funct_1(D_86))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.44  tff(c_216, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_3', '#skF_4', '#skF_6'))='#skF_7' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_208])).
% 2.88/1.44  tff(c_221, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_3', '#skF_4', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_216])).
% 2.88/1.44  tff(c_137, plain, (![D_66, E_62, C_63, A_64, B_65]: (r2_hidden('#skF_2'(E_62, C_63, A_64, B_65, D_66), C_63) | ~r2_hidden(E_62, k7_relset_1(A_64, B_65, D_66, C_63)) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_2(D_66, A_64, B_65) | ~v1_funct_1(D_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.88/1.44  tff(c_145, plain, (![E_62, C_63]: (r2_hidden('#skF_2'(E_62, C_63, '#skF_3', '#skF_4', '#skF_6'), C_63) | ~r2_hidden(E_62, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_63)) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_24, c_137])).
% 2.88/1.44  tff(c_226, plain, (![E_87, C_88]: (r2_hidden('#skF_2'(E_87, C_88, '#skF_3', '#skF_4', '#skF_6'), C_88) | ~r2_hidden(E_87, k7_relset_1('#skF_3', '#skF_4', '#skF_6', C_88)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_145])).
% 2.88/1.44  tff(c_20, plain, (![F_24]: (k1_funct_1('#skF_6', F_24)!='#skF_7' | ~r2_hidden(F_24, '#skF_5') | ~m1_subset_1(F_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.88/1.44  tff(c_249, plain, (![E_91]: (k1_funct_1('#skF_6', '#skF_2'(E_91, '#skF_5', '#skF_3', '#skF_4', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'(E_91, '#skF_5', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~r2_hidden(E_91, k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5')))), inference(resolution, [status(thm)], [c_226, c_20])).
% 2.88/1.44  tff(c_264, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_3', '#skF_4', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_22, c_249])).
% 2.88/1.44  tff(c_270, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_264])).
% 2.88/1.44  tff(c_651, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_648, c_270])).
% 2.88/1.44  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45, c_651])).
% 2.88/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.44  
% 2.88/1.44  Inference rules
% 2.88/1.44  ----------------------
% 2.88/1.44  #Ref     : 0
% 2.88/1.44  #Sup     : 149
% 2.88/1.44  #Fact    : 0
% 2.88/1.44  #Define  : 0
% 2.88/1.44  #Split   : 4
% 2.88/1.44  #Chain   : 0
% 2.88/1.44  #Close   : 0
% 2.88/1.44  
% 2.88/1.44  Ordering : KBO
% 2.88/1.44  
% 2.88/1.44  Simplification rules
% 2.88/1.44  ----------------------
% 2.88/1.44  #Subsume      : 14
% 2.88/1.44  #Demod        : 12
% 2.88/1.44  #Tautology    : 5
% 2.88/1.44  #SimpNegUnit  : 0
% 2.88/1.44  #BackRed      : 0
% 2.88/1.44  
% 2.88/1.44  #Partial instantiations: 0
% 2.88/1.44  #Strategies tried      : 1
% 2.88/1.44  
% 2.88/1.44  Timing (in seconds)
% 2.88/1.44  ----------------------
% 2.88/1.44  Preprocessing        : 0.27
% 2.88/1.44  Parsing              : 0.15
% 2.88/1.44  CNF conversion       : 0.02
% 2.88/1.44  Main loop            : 0.40
% 2.88/1.44  Inferencing          : 0.15
% 2.88/1.44  Reduction            : 0.10
% 2.88/1.44  Demodulation         : 0.07
% 2.88/1.44  BG Simplification    : 0.02
% 2.88/1.44  Subsumption          : 0.10
% 2.88/1.44  Abstraction          : 0.02
% 2.88/1.44  MUC search           : 0.00
% 2.88/1.44  Cooper               : 0.00
% 2.88/1.44  Total                : 0.70
% 2.88/1.44  Index Insertion      : 0.00
% 2.88/1.44  Index Deletion       : 0.00
% 2.88/1.44  Index Matching       : 0.00
% 2.88/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
