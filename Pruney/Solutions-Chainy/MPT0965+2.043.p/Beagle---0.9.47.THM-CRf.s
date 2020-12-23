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
% DateTime   : Thu Dec  3 10:11:06 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 121 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_75,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_78,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_81,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_60,c_78])).

tff(c_82,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_81])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [B_21,A_22] :
      ( v1_relat_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_50,plain,(
    ! [C_26,B_27,A_28] :
      ( v5_relat_1(C_26,B_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_28,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_50])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68,plain,(
    ! [B_39,C_40,A_41] :
      ( r2_hidden(k1_funct_1(B_39,C_40),A_41)
      | ~ r2_hidden(C_40,k1_relat_1(B_39))
      | ~ v1_funct_1(B_39)
      | ~ v5_relat_1(B_39,A_41)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_71,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_26])).

tff(c_74,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54,c_36,c_71])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.16  
% 1.91/1.16  %Foreground sorts:
% 1.91/1.16  
% 1.91/1.16  
% 1.91/1.16  %Background operators:
% 1.91/1.16  
% 1.91/1.16  
% 1.91/1.16  %Foreground operators:
% 1.91/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.91/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.91/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.91/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.91/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.91/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.91/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.16  
% 1.91/1.17  tff(f_86, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 1.91/1.17  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.91/1.17  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.91/1.17  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.91/1.17  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.91/1.17  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.91/1.17  tff(f_45, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 1.91/1.17  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.91/1.17  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.91/1.17  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.91/1.17  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.91/1.17  tff(c_56, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.91/1.17  tff(c_60, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_56])).
% 1.91/1.17  tff(c_75, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.91/1.17  tff(c_78, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_75])).
% 1.91/1.17  tff(c_81, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_60, c_78])).
% 1.91/1.17  tff(c_82, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_28, c_81])).
% 1.91/1.17  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.17  tff(c_38, plain, (![B_21, A_22]: (v1_relat_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.17  tff(c_41, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 1.91/1.17  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_41])).
% 1.91/1.17  tff(c_50, plain, (![C_26, B_27, A_28]: (v5_relat_1(C_26, B_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_28, B_27))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.17  tff(c_54, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_50])).
% 1.91/1.17  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.91/1.17  tff(c_68, plain, (![B_39, C_40, A_41]: (r2_hidden(k1_funct_1(B_39, C_40), A_41) | ~r2_hidden(C_40, k1_relat_1(B_39)) | ~v1_funct_1(B_39) | ~v5_relat_1(B_39, A_41) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.17  tff(c_26, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.91/1.17  tff(c_71, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_26])).
% 1.91/1.17  tff(c_74, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54, c_36, c_71])).
% 1.91/1.17  tff(c_83, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74])).
% 1.91/1.17  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_83])).
% 1.91/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  Inference rules
% 1.91/1.17  ----------------------
% 1.91/1.17  #Ref     : 0
% 1.91/1.17  #Sup     : 8
% 1.91/1.17  #Fact    : 0
% 1.91/1.17  #Define  : 0
% 1.91/1.17  #Split   : 0
% 1.91/1.17  #Chain   : 0
% 1.91/1.18  #Close   : 0
% 1.91/1.18  
% 1.91/1.18  Ordering : KBO
% 1.91/1.18  
% 1.91/1.18  Simplification rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Subsume      : 0
% 1.91/1.18  #Demod        : 9
% 1.91/1.18  #Tautology    : 2
% 1.91/1.18  #SimpNegUnit  : 1
% 1.91/1.18  #BackRed      : 2
% 1.91/1.18  
% 1.91/1.18  #Partial instantiations: 0
% 1.91/1.18  #Strategies tried      : 1
% 1.91/1.18  
% 1.91/1.18  Timing (in seconds)
% 1.91/1.18  ----------------------
% 1.91/1.18  Preprocessing        : 0.31
% 1.91/1.18  Parsing              : 0.16
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.11
% 1.91/1.18  Inferencing          : 0.04
% 1.91/1.18  Reduction            : 0.04
% 1.91/1.18  Demodulation         : 0.03
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.02
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.45
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.18  Index Matching       : 0.00
% 1.91/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
