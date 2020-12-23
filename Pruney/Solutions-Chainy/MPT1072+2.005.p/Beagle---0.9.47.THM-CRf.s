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
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 255 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_51,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_51])).

tff(c_87,plain,(
    ! [B_55,A_56,C_57] :
      ( k1_xboole_0 = B_55
      | k1_relset_1(A_56,B_55,C_57) = A_56
      | ~ v1_funct_2(C_57,A_56,B_55)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_90,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_87])).

tff(c_93,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_55,c_90])).

tff(c_94,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(k1_funct_1(B_4,A_3),k2_relat_1(B_4))
      | ~ r2_hidden(A_3,k1_relat_1(B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k3_funct_2(A_58,B_59,C_60,D_61) = k1_funct_1(C_60,D_61)
      | ~ m1_subset_1(D_61,A_58)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(C_60,A_58,B_59)
      | ~ v1_funct_1(C_60)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_108,plain,(
    ! [B_59,C_60] :
      ( k3_funct_2('#skF_1',B_59,C_60,'#skF_3') = k1_funct_1(C_60,'#skF_3')
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_59)))
      | ~ v1_funct_2(C_60,'#skF_1',B_59)
      | ~ v1_funct_1(C_60)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_104])).

tff(c_113,plain,(
    ! [B_62,C_63] :
      ( k3_funct_2('#skF_1',B_62,C_63,'#skF_3') = k1_funct_1(C_63,'#skF_3')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_62)))
      | ~ v1_funct_2(C_63,'#skF_1',B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_108])).

tff(c_116,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_119,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_116])).

tff(c_60,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_28,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_65,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_121,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_65])).

tff(c_128,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_134,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_94,c_128])).

tff(c_138,plain,
    ( v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_141,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_141])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_152,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.20  
% 2.14/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.20  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.14/1.20  
% 2.14/1.20  %Foreground sorts:
% 2.14/1.20  
% 2.14/1.20  
% 2.14/1.20  %Background operators:
% 2.14/1.20  
% 2.14/1.20  
% 2.14/1.20  %Foreground operators:
% 2.14/1.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.14/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.14/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.14/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.14/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.20  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.14/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.20  
% 2.14/1.22  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.14/1.22  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.14/1.22  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.22  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.14/1.22  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.14/1.22  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.14/1.22  tff(f_83, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.14/1.22  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.14/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.14/1.22  tff(c_38, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_36, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.22  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_42, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.22  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.14/1.22  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_51, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.22  tff(c_55, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_51])).
% 2.14/1.22  tff(c_87, plain, (![B_55, A_56, C_57]: (k1_xboole_0=B_55 | k1_relset_1(A_56, B_55, C_57)=A_56 | ~v1_funct_2(C_57, A_56, B_55) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.22  tff(c_90, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_87])).
% 2.14/1.22  tff(c_93, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_55, c_90])).
% 2.14/1.22  tff(c_94, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_93])).
% 2.14/1.22  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(k1_funct_1(B_4, A_3), k2_relat_1(B_4)) | ~r2_hidden(A_3, k1_relat_1(B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.22  tff(c_104, plain, (![A_58, B_59, C_60, D_61]: (k3_funct_2(A_58, B_59, C_60, D_61)=k1_funct_1(C_60, D_61) | ~m1_subset_1(D_61, A_58) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(C_60, A_58, B_59) | ~v1_funct_1(C_60) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.22  tff(c_108, plain, (![B_59, C_60]: (k3_funct_2('#skF_1', B_59, C_60, '#skF_3')=k1_funct_1(C_60, '#skF_3') | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_59))) | ~v1_funct_2(C_60, '#skF_1', B_59) | ~v1_funct_1(C_60) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_104])).
% 2.14/1.22  tff(c_113, plain, (![B_62, C_63]: (k3_funct_2('#skF_1', B_62, C_63, '#skF_3')=k1_funct_1(C_63, '#skF_3') | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_62))) | ~v1_funct_2(C_63, '#skF_1', B_62) | ~v1_funct_1(C_63))), inference(negUnitSimplification, [status(thm)], [c_40, c_108])).
% 2.14/1.22  tff(c_116, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_113])).
% 2.14/1.22  tff(c_119, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_116])).
% 2.14/1.22  tff(c_60, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.22  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_60])).
% 2.14/1.22  tff(c_28, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.14/1.22  tff(c_65, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28])).
% 2.14/1.22  tff(c_121, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_65])).
% 2.14/1.22  tff(c_128, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_121])).
% 2.14/1.22  tff(c_134, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_94, c_128])).
% 2.14/1.22  tff(c_138, plain, (v1_xboole_0('#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_4, c_134])).
% 2.14/1.22  tff(c_141, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_138])).
% 2.14/1.22  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_141])).
% 2.14/1.22  tff(c_144, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_93])).
% 2.14/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.14/1.22  tff(c_152, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_2])).
% 2.14/1.22  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_152])).
% 2.14/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.22  
% 2.14/1.22  Inference rules
% 2.14/1.22  ----------------------
% 2.14/1.22  #Ref     : 0
% 2.14/1.22  #Sup     : 23
% 2.14/1.22  #Fact    : 0
% 2.14/1.22  #Define  : 0
% 2.14/1.22  #Split   : 2
% 2.14/1.22  #Chain   : 0
% 2.14/1.22  #Close   : 0
% 2.14/1.22  
% 2.14/1.22  Ordering : KBO
% 2.14/1.22  
% 2.14/1.22  Simplification rules
% 2.14/1.22  ----------------------
% 2.14/1.22  #Subsume      : 1
% 2.14/1.22  #Demod        : 36
% 2.14/1.22  #Tautology    : 11
% 2.14/1.22  #SimpNegUnit  : 3
% 2.14/1.22  #BackRed      : 11
% 2.14/1.22  
% 2.14/1.22  #Partial instantiations: 0
% 2.14/1.22  #Strategies tried      : 1
% 2.14/1.22  
% 2.14/1.22  Timing (in seconds)
% 2.14/1.22  ----------------------
% 2.14/1.22  Preprocessing        : 0.32
% 2.14/1.22  Parsing              : 0.17
% 2.14/1.22  CNF conversion       : 0.02
% 2.14/1.22  Main loop            : 0.17
% 2.14/1.22  Inferencing          : 0.06
% 2.14/1.22  Reduction            : 0.06
% 2.14/1.22  Demodulation         : 0.04
% 2.14/1.22  BG Simplification    : 0.01
% 2.14/1.22  Subsumption          : 0.03
% 2.14/1.22  Abstraction          : 0.01
% 2.14/1.22  MUC search           : 0.00
% 2.14/1.22  Cooper               : 0.00
% 2.14/1.22  Total                : 0.53
% 2.14/1.22  Index Insertion      : 0.00
% 2.14/1.22  Index Deletion       : 0.00
% 2.14/1.22  Index Matching       : 0.00
% 2.14/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
