%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 176 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( ? [F] :
                  ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) )
             => r2_hidden(E,k7_relset_1(A,B,D,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(A,B) )
       => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_28,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_43,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    r2_hidden('#skF_6','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_91,plain,(
    ! [B_46,A_47,C_48] :
      ( k1_xboole_0 = B_46
      | k1_relset_1(A_47,B_46,C_48) = A_47
      | ~ v1_funct_2(C_48,A_47,B_46)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_97,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_61,c_94])).

tff(c_98,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_97])).

tff(c_26,plain,(
    k1_funct_1('#skF_4','#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_108,plain,(
    ! [C_49,A_50,B_51] :
      ( r2_hidden(k1_funct_1(C_49,A_50),k2_relat_1(k7_relat_1(C_49,B_51)))
      | ~ r2_hidden(A_50,B_51)
      | ~ r2_hidden(A_50,k1_relat_1(C_49))
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_5',k2_relat_1(k7_relat_1('#skF_4',B_51)))
      | ~ r2_hidden('#skF_6',B_51)
      | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_117,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_5',k2_relat_1(k7_relat_1('#skF_4',B_52)))
      | ~ r2_hidden('#skF_6',B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_38,c_30,c_98,c_114])).

tff(c_121,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_5',k9_relat_1('#skF_4',A_1))
      | ~ r2_hidden('#skF_6',A_1)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_124,plain,(
    ! [A_53] :
      ( r2_hidden('#skF_5',k9_relat_1('#skF_4',A_53))
      | ~ r2_hidden('#skF_6',A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_121])).

tff(c_68,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( k7_relset_1(A_34,B_35,C_36,D_37) = k9_relat_1(C_36,D_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [D_37] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_37) = k9_relat_1('#skF_4',D_37) ),
    inference(resolution,[status(thm)],[c_34,c_68])).

tff(c_24,plain,(
    ~ r2_hidden('#skF_5',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_5',k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_24])).

tff(c_127,plain,(
    ~ r2_hidden('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_72])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:38:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.12  
% 1.87/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.13  
% 1.87/1.13  %Foreground sorts:
% 1.87/1.13  
% 1.87/1.13  
% 1.87/1.13  %Background operators:
% 1.87/1.13  
% 1.87/1.13  
% 1.87/1.13  %Foreground operators:
% 1.87/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.13  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.87/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.87/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.87/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.87/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.87/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.13  
% 1.87/1.14  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_2)).
% 1.87/1.14  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.87/1.14  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.87/1.14  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.87/1.14  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.87/1.14  tff(f_39, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 1.87/1.14  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.87/1.14  tff(c_28, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_43, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.14  tff(c_47, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_43])).
% 1.87/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.14  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_30, plain, (r2_hidden('#skF_6', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_36, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_57, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.14  tff(c_61, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_57])).
% 1.87/1.14  tff(c_91, plain, (![B_46, A_47, C_48]: (k1_xboole_0=B_46 | k1_relset_1(A_47, B_46, C_48)=A_47 | ~v1_funct_2(C_48, A_47, B_46) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.14  tff(c_94, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_91])).
% 1.87/1.14  tff(c_97, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_61, c_94])).
% 1.87/1.14  tff(c_98, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_32, c_97])).
% 1.87/1.14  tff(c_26, plain, (k1_funct_1('#skF_4', '#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_108, plain, (![C_49, A_50, B_51]: (r2_hidden(k1_funct_1(C_49, A_50), k2_relat_1(k7_relat_1(C_49, B_51))) | ~r2_hidden(A_50, B_51) | ~r2_hidden(A_50, k1_relat_1(C_49)) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.14  tff(c_114, plain, (![B_51]: (r2_hidden('#skF_5', k2_relat_1(k7_relat_1('#skF_4', B_51))) | ~r2_hidden('#skF_6', B_51) | ~r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_108])).
% 1.87/1.14  tff(c_117, plain, (![B_52]: (r2_hidden('#skF_5', k2_relat_1(k7_relat_1('#skF_4', B_52))) | ~r2_hidden('#skF_6', B_52))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_38, c_30, c_98, c_114])).
% 1.87/1.14  tff(c_121, plain, (![A_1]: (r2_hidden('#skF_5', k9_relat_1('#skF_4', A_1)) | ~r2_hidden('#skF_6', A_1) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 1.87/1.14  tff(c_124, plain, (![A_53]: (r2_hidden('#skF_5', k9_relat_1('#skF_4', A_53)) | ~r2_hidden('#skF_6', A_53))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_121])).
% 1.87/1.14  tff(c_68, plain, (![A_34, B_35, C_36, D_37]: (k7_relset_1(A_34, B_35, C_36, D_37)=k9_relat_1(C_36, D_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.14  tff(c_71, plain, (![D_37]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_37)=k9_relat_1('#skF_4', D_37))), inference(resolution, [status(thm)], [c_34, c_68])).
% 1.87/1.14  tff(c_24, plain, (~r2_hidden('#skF_5', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.87/1.14  tff(c_72, plain, (~r2_hidden('#skF_5', k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_24])).
% 1.87/1.14  tff(c_127, plain, (~r2_hidden('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_124, c_72])).
% 1.87/1.14  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_127])).
% 1.87/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.14  
% 1.87/1.14  Inference rules
% 1.87/1.14  ----------------------
% 1.87/1.14  #Ref     : 0
% 1.87/1.14  #Sup     : 21
% 1.87/1.14  #Fact    : 0
% 1.87/1.14  #Define  : 0
% 1.87/1.14  #Split   : 0
% 1.87/1.14  #Chain   : 0
% 1.87/1.14  #Close   : 0
% 1.87/1.14  
% 1.87/1.14  Ordering : KBO
% 1.87/1.14  
% 1.87/1.14  Simplification rules
% 1.87/1.14  ----------------------
% 1.87/1.14  #Subsume      : 0
% 1.87/1.14  #Demod        : 12
% 1.87/1.14  #Tautology    : 13
% 1.87/1.14  #SimpNegUnit  : 2
% 1.87/1.14  #BackRed      : 2
% 1.87/1.14  
% 1.87/1.14  #Partial instantiations: 0
% 1.87/1.14  #Strategies tried      : 1
% 1.87/1.14  
% 1.87/1.14  Timing (in seconds)
% 1.87/1.14  ----------------------
% 1.87/1.14  Preprocessing        : 0.30
% 1.87/1.14  Parsing              : 0.16
% 1.87/1.14  CNF conversion       : 0.02
% 1.87/1.14  Main loop            : 0.14
% 1.87/1.14  Inferencing          : 0.05
% 1.87/1.14  Reduction            : 0.04
% 1.87/1.14  Demodulation         : 0.03
% 1.87/1.14  BG Simplification    : 0.01
% 1.87/1.14  Subsumption          : 0.02
% 1.87/1.14  Abstraction          : 0.01
% 1.87/1.14  MUC search           : 0.00
% 1.87/1.14  Cooper               : 0.00
% 1.87/1.14  Total                : 0.46
% 1.87/1.14  Index Insertion      : 0.00
% 1.87/1.14  Index Deletion       : 0.00
% 1.87/1.14  Index Matching       : 0.00
% 1.87/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
