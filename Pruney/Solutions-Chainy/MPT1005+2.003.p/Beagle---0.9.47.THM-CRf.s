%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:59 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 180 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 282 expanded)
%              Number of equality atoms :   30 ( 109 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_43,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_30,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_55])).

tff(c_22,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_299,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | v1_xboole_0(B_63)
      | ~ m1_subset_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_303,plain,(
    ! [A_62,A_4] :
      ( A_62 = A_4
      | v1_xboole_0(k1_tarski(A_4))
      | ~ m1_subset_1(A_62,k1_tarski(A_4)) ) ),
    inference(resolution,[status(thm)],[c_299,c_10])).

tff(c_318,plain,(
    ! [A_67,A_66] :
      ( A_67 = A_66
      | ~ m1_subset_1(A_66,k1_tarski(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_303])).

tff(c_327,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_318])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_151,plain,(
    ! [A_43,A_4] :
      ( A_43 = A_4
      | v1_xboole_0(k1_tarski(A_4))
      | ~ m1_subset_1(A_43,k1_tarski(A_4)) ) ),
    inference(resolution,[status(thm)],[c_147,c_10])).

tff(c_155,plain,(
    ! [A_46,A_45] :
      ( A_46 = A_45
      | ~ m1_subset_1(A_45,k1_tarski(A_46)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_151])).

tff(c_164,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_155])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_105,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k9_relat_1(B_36,A_37),k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    ! [A_37] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_37),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_105])).

tff(c_109,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_167,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_109])).

tff(c_32,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_217,plain,(
    ! [A_52] : m1_subset_1('#skF_5',k1_zfmisc_1(A_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_32])).

tff(c_44,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_221,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_217,c_44])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_221])).

tff(c_243,plain,(
    ! [A_55] : r1_tarski(k9_relat_1(k1_xboole_0,A_55),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,(
    ! [A_55] :
      ( k9_relat_1(k1_xboole_0,A_55) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_55)) ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_248,plain,(
    ! [A_55] : k9_relat_1(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_245])).

tff(c_331,plain,(
    ! [A_55] : k9_relat_1('#skF_5',A_55) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_327,c_248])).

tff(c_335,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_32])).

tff(c_1040,plain,(
    ! [A_761,B_762,C_763,D_764] :
      ( k7_relset_1(A_761,B_762,C_763,D_764) = k9_relat_1(C_763,D_764)
      | ~ m1_subset_1(C_763,k1_zfmisc_1(k2_zfmisc_1(A_761,B_762))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1043,plain,(
    ! [A_761,B_762,D_764] : k7_relset_1(A_761,B_762,'#skF_5',D_764) = k9_relat_1('#skF_5',D_764) ),
    inference(resolution,[status(thm)],[c_335,c_1040])).

tff(c_1049,plain,(
    ! [A_761,B_762,D_764] : k7_relset_1(A_761,B_762,'#skF_5',D_764) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_1043])).

tff(c_48,plain,(
    k7_relset_1(k1_xboole_0,'#skF_3','#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_333,plain,(
    k7_relset_1('#skF_5','#skF_3','#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_327,c_48])).

tff(c_1054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.44  
% 2.95/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.44  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.95/1.44  
% 2.95/1.44  %Foreground sorts:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Background operators:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Foreground operators:
% 2.95/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.95/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.95/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.95/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.95/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.95/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.44  
% 3.08/1.46  tff(f_50, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 3.08/1.46  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.08/1.46  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 3.08/1.46  tff(f_43, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.08/1.46  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.08/1.46  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.08/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.08/1.46  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.08/1.46  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.08/1.46  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.08/1.46  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.08/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.08/1.46  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/1.46  tff(c_30, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.08/1.46  tff(c_28, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.08/1.46  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.46  tff(c_55, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50])).
% 3.08/1.46  tff(c_56, plain, (m1_subset_1('#skF_5', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_55])).
% 3.08/1.46  tff(c_22, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.08/1.46  tff(c_299, plain, (![A_62, B_63]: (r2_hidden(A_62, B_63) | v1_xboole_0(B_63) | ~m1_subset_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.46  tff(c_10, plain, (![C_8, A_4]: (C_8=A_4 | ~r2_hidden(C_8, k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.08/1.46  tff(c_303, plain, (![A_62, A_4]: (A_62=A_4 | v1_xboole_0(k1_tarski(A_4)) | ~m1_subset_1(A_62, k1_tarski(A_4)))), inference(resolution, [status(thm)], [c_299, c_10])).
% 3.08/1.46  tff(c_318, plain, (![A_67, A_66]: (A_67=A_66 | ~m1_subset_1(A_66, k1_tarski(A_67)))), inference(negUnitSimplification, [status(thm)], [c_22, c_303])).
% 3.08/1.46  tff(c_327, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_318])).
% 3.08/1.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.46  tff(c_147, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.08/1.46  tff(c_151, plain, (![A_43, A_4]: (A_43=A_4 | v1_xboole_0(k1_tarski(A_4)) | ~m1_subset_1(A_43, k1_tarski(A_4)))), inference(resolution, [status(thm)], [c_147, c_10])).
% 3.08/1.46  tff(c_155, plain, (![A_46, A_45]: (A_46=A_45 | ~m1_subset_1(A_45, k1_tarski(A_46)))), inference(negUnitSimplification, [status(thm)], [c_22, c_151])).
% 3.08/1.46  tff(c_164, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_56, c_155])).
% 3.08/1.46  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.46  tff(c_105, plain, (![B_36, A_37]: (r1_tarski(k9_relat_1(B_36, A_37), k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.08/1.46  tff(c_108, plain, (![A_37]: (r1_tarski(k9_relat_1(k1_xboole_0, A_37), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_105])).
% 3.08/1.46  tff(c_109, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_108])).
% 3.08/1.46  tff(c_167, plain, (~v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_109])).
% 3.08/1.46  tff(c_32, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.08/1.46  tff(c_217, plain, (![A_52]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_52)))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_32])).
% 3.08/1.46  tff(c_44, plain, (![C_22, A_20, B_21]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.08/1.46  tff(c_221, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_217, c_44])).
% 3.08/1.46  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_221])).
% 3.08/1.46  tff(c_243, plain, (![A_55]: (r1_tarski(k9_relat_1(k1_xboole_0, A_55), k1_xboole_0))), inference(splitRight, [status(thm)], [c_108])).
% 3.08/1.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.46  tff(c_245, plain, (![A_55]: (k9_relat_1(k1_xboole_0, A_55)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_55)))), inference(resolution, [status(thm)], [c_243, c_2])).
% 3.08/1.46  tff(c_248, plain, (![A_55]: (k9_relat_1(k1_xboole_0, A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_245])).
% 3.08/1.46  tff(c_331, plain, (![A_55]: (k9_relat_1('#skF_5', A_55)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_327, c_248])).
% 3.08/1.46  tff(c_335, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_32])).
% 3.08/1.46  tff(c_1040, plain, (![A_761, B_762, C_763, D_764]: (k7_relset_1(A_761, B_762, C_763, D_764)=k9_relat_1(C_763, D_764) | ~m1_subset_1(C_763, k1_zfmisc_1(k2_zfmisc_1(A_761, B_762))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.46  tff(c_1043, plain, (![A_761, B_762, D_764]: (k7_relset_1(A_761, B_762, '#skF_5', D_764)=k9_relat_1('#skF_5', D_764))), inference(resolution, [status(thm)], [c_335, c_1040])).
% 3.08/1.46  tff(c_1049, plain, (![A_761, B_762, D_764]: (k7_relset_1(A_761, B_762, '#skF_5', D_764)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_1043])).
% 3.08/1.46  tff(c_48, plain, (k7_relset_1(k1_xboole_0, '#skF_3', '#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.08/1.46  tff(c_333, plain, (k7_relset_1('#skF_5', '#skF_3', '#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_327, c_327, c_48])).
% 3.08/1.46  tff(c_1054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1049, c_333])).
% 3.08/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  Inference rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Ref     : 0
% 3.08/1.46  #Sup     : 224
% 3.08/1.46  #Fact    : 1
% 3.08/1.46  #Define  : 0
% 3.08/1.46  #Split   : 2
% 3.08/1.46  #Chain   : 0
% 3.08/1.46  #Close   : 0
% 3.08/1.46  
% 3.08/1.46  Ordering : KBO
% 3.08/1.46  
% 3.08/1.46  Simplification rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Subsume      : 22
% 3.08/1.46  #Demod        : 88
% 3.08/1.46  #Tautology    : 85
% 3.08/1.46  #SimpNegUnit  : 3
% 3.08/1.46  #BackRed      : 32
% 3.08/1.46  
% 3.08/1.46  #Partial instantiations: 507
% 3.08/1.46  #Strategies tried      : 1
% 3.08/1.46  
% 3.08/1.46  Timing (in seconds)
% 3.08/1.46  ----------------------
% 3.08/1.46  Preprocessing        : 0.32
% 3.08/1.46  Parsing              : 0.17
% 3.08/1.46  CNF conversion       : 0.02
% 3.08/1.46  Main loop            : 0.38
% 3.08/1.46  Inferencing          : 0.16
% 3.08/1.46  Reduction            : 0.10
% 3.08/1.46  Demodulation         : 0.07
% 3.08/1.46  BG Simplification    : 0.02
% 3.08/1.46  Subsumption          : 0.07
% 3.08/1.46  Abstraction          : 0.02
% 3.08/1.46  MUC search           : 0.00
% 3.08/1.46  Cooper               : 0.00
% 3.08/1.46  Total                : 0.73
% 3.08/1.46  Index Insertion      : 0.00
% 3.08/1.46  Index Deletion       : 0.00
% 3.08/1.46  Index Matching       : 0.00
% 3.08/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
