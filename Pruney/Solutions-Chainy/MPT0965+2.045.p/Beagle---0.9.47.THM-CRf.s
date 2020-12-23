%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:06 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 126 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    ! [C_24,B_25,A_26] :
      ( v5_relat_1(C_24,B_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_26,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_39,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_28])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_relset_1(A_30,B_31,C_32) = k2_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_45])).

tff(c_55,plain,(
    ! [D_36,C_37,A_38,B_39] :
      ( r2_hidden(k1_funct_1(D_36,C_37),k2_relset_1(A_38,B_39,D_36))
      | k1_xboole_0 = B_39
      | ~ r2_hidden(C_37,A_38)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(D_36,A_38,B_39)
      | ~ v1_funct_1(D_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [C_37] :
      ( r2_hidden(k1_funct_1('#skF_4',C_37),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_37,'#skF_1')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_55])).

tff(c_60,plain,(
    ! [C_37] :
      ( r2_hidden(k1_funct_1('#skF_4',C_37),k2_relat_1('#skF_4'))
      | k1_xboole_0 = '#skF_2'
      | ~ r2_hidden(C_37,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_58])).

tff(c_62,plain,(
    ! [C_40] :
      ( r2_hidden(k1_funct_1('#skF_4',C_40),k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_40,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_60])).

tff(c_6,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,k2_relat_1(B_7))
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    ! [C_40,A_6] :
      ( r2_hidden(k1_funct_1('#skF_4',C_40),A_6)
      | ~ v5_relat_1('#skF_4',A_6)
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(C_40,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_62,c_6])).

tff(c_68,plain,(
    ! [C_41,A_42] :
      ( r2_hidden(k1_funct_1('#skF_4',C_41),A_42)
      | ~ v5_relat_1('#skF_4',A_42)
      | ~ r2_hidden(C_41,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_64])).

tff(c_16,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_16])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_39,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.98/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.98/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.98/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.19  
% 2.09/1.21  tff(f_78, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.09/1.21  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.09/1.21  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.09/1.21  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.09/1.21  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.09/1.21  tff(f_65, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 2.09/1.21  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 2.09/1.21  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.21  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.21  tff(c_35, plain, (![C_24, B_25, A_26]: (v5_relat_1(C_24, B_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_26, B_25))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.21  tff(c_39, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_35])).
% 2.09/1.21  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.21  tff(c_28, plain, (![B_22, A_23]: (v1_relat_1(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(A_23)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.21  tff(c_31, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_28])).
% 2.09/1.21  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_31])).
% 2.09/1.21  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.21  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.21  tff(c_24, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.21  tff(c_45, plain, (![A_30, B_31, C_32]: (k2_relset_1(A_30, B_31, C_32)=k2_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.21  tff(c_49, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_45])).
% 2.09/1.21  tff(c_55, plain, (![D_36, C_37, A_38, B_39]: (r2_hidden(k1_funct_1(D_36, C_37), k2_relset_1(A_38, B_39, D_36)) | k1_xboole_0=B_39 | ~r2_hidden(C_37, A_38) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(D_36, A_38, B_39) | ~v1_funct_1(D_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.09/1.21  tff(c_58, plain, (![C_37]: (r2_hidden(k1_funct_1('#skF_4', C_37), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_2' | ~r2_hidden(C_37, '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_55])).
% 2.09/1.21  tff(c_60, plain, (![C_37]: (r2_hidden(k1_funct_1('#skF_4', C_37), k2_relat_1('#skF_4')) | k1_xboole_0='#skF_2' | ~r2_hidden(C_37, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_58])).
% 2.09/1.21  tff(c_62, plain, (![C_40]: (r2_hidden(k1_funct_1('#skF_4', C_40), k2_relat_1('#skF_4')) | ~r2_hidden(C_40, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_18, c_60])).
% 2.09/1.21  tff(c_6, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, k2_relat_1(B_7)) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.21  tff(c_64, plain, (![C_40, A_6]: (r2_hidden(k1_funct_1('#skF_4', C_40), A_6) | ~v5_relat_1('#skF_4', A_6) | ~v1_relat_1('#skF_4') | ~r2_hidden(C_40, '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_6])).
% 2.09/1.21  tff(c_68, plain, (![C_41, A_42]: (r2_hidden(k1_funct_1('#skF_4', C_41), A_42) | ~v5_relat_1('#skF_4', A_42) | ~r2_hidden(C_41, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_64])).
% 2.09/1.21  tff(c_16, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.21  tff(c_74, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_16])).
% 2.09/1.21  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_39, c_74])).
% 2.09/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  Inference rules
% 2.09/1.21  ----------------------
% 2.09/1.21  #Ref     : 0
% 2.09/1.21  #Sup     : 10
% 2.09/1.21  #Fact    : 0
% 2.09/1.21  #Define  : 0
% 2.09/1.21  #Split   : 0
% 2.09/1.21  #Chain   : 0
% 2.09/1.21  #Close   : 0
% 2.09/1.21  
% 2.09/1.21  Ordering : KBO
% 2.09/1.21  
% 2.09/1.21  Simplification rules
% 2.09/1.21  ----------------------
% 2.09/1.21  #Subsume      : 0
% 2.09/1.21  #Demod        : 7
% 2.09/1.21  #Tautology    : 2
% 2.09/1.21  #SimpNegUnit  : 1
% 2.09/1.21  #BackRed      : 0
% 2.09/1.21  
% 2.09/1.21  #Partial instantiations: 0
% 2.09/1.21  #Strategies tried      : 1
% 2.09/1.21  
% 2.09/1.21  Timing (in seconds)
% 2.09/1.21  ----------------------
% 2.09/1.21  Preprocessing        : 0.32
% 2.09/1.21  Parsing              : 0.17
% 2.09/1.21  CNF conversion       : 0.02
% 2.09/1.21  Main loop            : 0.12
% 2.09/1.21  Inferencing          : 0.05
% 2.09/1.21  Reduction            : 0.04
% 2.09/1.21  Demodulation         : 0.03
% 2.09/1.21  BG Simplification    : 0.01
% 2.09/1.21  Subsumption          : 0.01
% 2.09/1.21  Abstraction          : 0.00
% 2.09/1.21  MUC search           : 0.00
% 2.09/1.21  Cooper               : 0.00
% 2.09/1.21  Total                : 0.47
% 2.09/1.21  Index Insertion      : 0.00
% 2.09/1.21  Index Deletion       : 0.00
% 2.09/1.21  Index Matching       : 0.00
% 2.09/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
