%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:35 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 130 expanded)
%              Number of leaves         :   37 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 315 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_34,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1231,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k3_funct_2(A_189,B_190,C_191,D_192) = k1_funct_1(C_191,D_192)
      | ~ m1_subset_1(D_192,A_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_2(C_191,A_189,B_190)
      | ~ v1_funct_1(C_191)
      | v1_xboole_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1243,plain,(
    ! [B_190,C_191] :
      ( k3_funct_2('#skF_2',B_190,C_191,'#skF_5') = k1_funct_1(C_191,'#skF_5')
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_190)))
      | ~ v1_funct_2(C_191,'#skF_2',B_190)
      | ~ v1_funct_1(C_191)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_1231])).

tff(c_1255,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2('#skF_2',B_195,C_196,'#skF_5') = k1_funct_1(C_196,'#skF_5')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_195)))
      | ~ v1_funct_2(C_196,'#skF_2',B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1243])).

tff(c_1262,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1255])).

tff(c_1274,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1262])).

tff(c_42,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1277,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_42])).

tff(c_188,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_205,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_188])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_374,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_391,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_374])).

tff(c_870,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_877,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_870])).

tff(c_889,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_391,c_877])).

tff(c_893,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_889])).

tff(c_1039,plain,(
    ! [A_179,B_180,C_181] :
      ( k7_partfun1(A_179,B_180,C_181) = k1_funct_1(B_180,C_181)
      | ~ r2_hidden(C_181,k1_relat_1(B_180))
      | ~ v1_funct_1(B_180)
      | ~ v5_relat_1(B_180,A_179)
      | ~ v1_relat_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1041,plain,(
    ! [A_179,C_181] :
      ( k7_partfun1(A_179,'#skF_4',C_181) = k1_funct_1('#skF_4',C_181)
      | ~ r2_hidden(C_181,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_179)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_1039])).

tff(c_1780,plain,(
    ! [A_218,C_219] :
      ( k7_partfun1(A_218,'#skF_4',C_219) = k1_funct_1('#skF_4',C_219)
      | ~ r2_hidden(C_219,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_50,c_1041])).

tff(c_1783,plain,(
    ! [A_218,A_7] :
      ( k7_partfun1(A_218,'#skF_4',A_7) = k1_funct_1('#skF_4',A_7)
      | ~ v5_relat_1('#skF_4',A_218)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1780])).

tff(c_1841,plain,(
    ! [A_225,A_226] :
      ( k7_partfun1(A_225,'#skF_4',A_226) = k1_funct_1('#skF_4',A_226)
      | ~ v5_relat_1('#skF_4',A_225)
      | ~ m1_subset_1(A_226,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1783])).

tff(c_1849,plain,(
    ! [A_227] :
      ( k7_partfun1('#skF_3','#skF_4',A_227) = k1_funct_1('#skF_4',A_227)
      | ~ m1_subset_1(A_227,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_205,c_1841])).

tff(c_1860,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1849])).

tff(c_1866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1277,c_1860])).

tff(c_1867,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_889])).

tff(c_4,plain,(
    ! [A_4] : m1_subset_1('#skF_1'(A_4),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_121,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,B_67)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,(
    ! [B_68,A_69] :
      ( ~ r1_tarski(B_68,A_69)
      | v1_xboole_0(B_68)
      | ~ m1_subset_1(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_121,c_16])).

tff(c_138,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_79,c_126])).

tff(c_140,plain,(
    ! [A_70] : ~ m1_subset_1(A_70,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_145,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_146,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1897,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_146])).

tff(c_1903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.68  
% 3.99/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.99/1.68  
% 3.99/1.68  %Foreground sorts:
% 3.99/1.68  
% 3.99/1.68  
% 3.99/1.68  %Background operators:
% 3.99/1.68  
% 3.99/1.68  
% 3.99/1.68  %Foreground operators:
% 3.99/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.99/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.99/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.68  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.99/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.99/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.99/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.99/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.99/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.99/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.99/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.99/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.99/1.68  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.99/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.99/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.68  
% 4.25/1.70  tff(f_133, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 4.25/1.70  tff(f_113, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.25/1.70  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.25/1.70  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.25/1.70  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.25/1.70  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.25/1.70  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.25/1.70  tff(f_100, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 4.25/1.70  tff(f_34, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.25/1.70  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.25/1.70  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.25/1.70  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.25/1.70  tff(c_52, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_44, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_1231, plain, (![A_189, B_190, C_191, D_192]: (k3_funct_2(A_189, B_190, C_191, D_192)=k1_funct_1(C_191, D_192) | ~m1_subset_1(D_192, A_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_2(C_191, A_189, B_190) | ~v1_funct_1(C_191) | v1_xboole_0(A_189))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.25/1.70  tff(c_1243, plain, (![B_190, C_191]: (k3_funct_2('#skF_2', B_190, C_191, '#skF_5')=k1_funct_1(C_191, '#skF_5') | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_190))) | ~v1_funct_2(C_191, '#skF_2', B_190) | ~v1_funct_1(C_191) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_1231])).
% 4.25/1.70  tff(c_1255, plain, (![B_195, C_196]: (k3_funct_2('#skF_2', B_195, C_196, '#skF_5')=k1_funct_1(C_196, '#skF_5') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_195))) | ~v1_funct_2(C_196, '#skF_2', B_195) | ~v1_funct_1(C_196))), inference(negUnitSimplification, [status(thm)], [c_54, c_1243])).
% 4.25/1.70  tff(c_1262, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1255])).
% 4.25/1.70  tff(c_1274, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1262])).
% 4.25/1.70  tff(c_42, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.25/1.70  tff(c_1277, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1274, c_42])).
% 4.25/1.70  tff(c_188, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.25/1.70  tff(c_205, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_188])).
% 4.25/1.70  tff(c_8, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.25/1.70  tff(c_82, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.25/1.70  tff(c_99, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_82])).
% 4.25/1.70  tff(c_374, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.25/1.70  tff(c_391, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_374])).
% 4.25/1.70  tff(c_870, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.25/1.70  tff(c_877, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_870])).
% 4.25/1.70  tff(c_889, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_391, c_877])).
% 4.25/1.70  tff(c_893, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_889])).
% 4.25/1.70  tff(c_1039, plain, (![A_179, B_180, C_181]: (k7_partfun1(A_179, B_180, C_181)=k1_funct_1(B_180, C_181) | ~r2_hidden(C_181, k1_relat_1(B_180)) | ~v1_funct_1(B_180) | ~v5_relat_1(B_180, A_179) | ~v1_relat_1(B_180))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.25/1.70  tff(c_1041, plain, (![A_179, C_181]: (k7_partfun1(A_179, '#skF_4', C_181)=k1_funct_1('#skF_4', C_181) | ~r2_hidden(C_181, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_179) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_893, c_1039])).
% 4.25/1.70  tff(c_1780, plain, (![A_218, C_219]: (k7_partfun1(A_218, '#skF_4', C_219)=k1_funct_1('#skF_4', C_219) | ~r2_hidden(C_219, '#skF_2') | ~v5_relat_1('#skF_4', A_218))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_50, c_1041])).
% 4.25/1.70  tff(c_1783, plain, (![A_218, A_7]: (k7_partfun1(A_218, '#skF_4', A_7)=k1_funct_1('#skF_4', A_7) | ~v5_relat_1('#skF_4', A_218) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1780])).
% 4.25/1.70  tff(c_1841, plain, (![A_225, A_226]: (k7_partfun1(A_225, '#skF_4', A_226)=k1_funct_1('#skF_4', A_226) | ~v5_relat_1('#skF_4', A_225) | ~m1_subset_1(A_226, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1783])).
% 4.25/1.70  tff(c_1849, plain, (![A_227]: (k7_partfun1('#skF_3', '#skF_4', A_227)=k1_funct_1('#skF_4', A_227) | ~m1_subset_1(A_227, '#skF_2'))), inference(resolution, [status(thm)], [c_205, c_1841])).
% 4.25/1.70  tff(c_1860, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1849])).
% 4.25/1.70  tff(c_1866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1277, c_1860])).
% 4.25/1.70  tff(c_1867, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_889])).
% 4.25/1.70  tff(c_4, plain, (![A_4]: (m1_subset_1('#skF_1'(A_4), A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.25/1.70  tff(c_6, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.25/1.70  tff(c_62, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.25/1.70  tff(c_79, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_6, c_62])).
% 4.25/1.70  tff(c_121, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | v1_xboole_0(B_67) | ~m1_subset_1(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.25/1.70  tff(c_16, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.25/1.70  tff(c_126, plain, (![B_68, A_69]: (~r1_tarski(B_68, A_69) | v1_xboole_0(B_68) | ~m1_subset_1(A_69, B_68))), inference(resolution, [status(thm)], [c_121, c_16])).
% 4.25/1.70  tff(c_138, plain, (![A_6]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_79, c_126])).
% 4.25/1.70  tff(c_140, plain, (![A_70]: (~m1_subset_1(A_70, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_138])).
% 4.25/1.70  tff(c_145, plain, $false, inference(resolution, [status(thm)], [c_4, c_140])).
% 4.25/1.70  tff(c_146, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_138])).
% 4.25/1.70  tff(c_1897, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_146])).
% 4.25/1.70  tff(c_1903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1897])).
% 4.25/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.25/1.70  
% 4.25/1.70  Inference rules
% 4.25/1.70  ----------------------
% 4.25/1.70  #Ref     : 0
% 4.25/1.70  #Sup     : 368
% 4.25/1.70  #Fact    : 0
% 4.25/1.70  #Define  : 0
% 4.25/1.70  #Split   : 14
% 4.25/1.70  #Chain   : 0
% 4.25/1.70  #Close   : 0
% 4.25/1.70  
% 4.25/1.70  Ordering : KBO
% 4.25/1.70  
% 4.25/1.70  Simplification rules
% 4.25/1.70  ----------------------
% 4.25/1.70  #Subsume      : 19
% 4.25/1.70  #Demod        : 252
% 4.25/1.70  #Tautology    : 128
% 4.25/1.70  #SimpNegUnit  : 8
% 4.25/1.70  #BackRed      : 55
% 4.25/1.70  
% 4.25/1.70  #Partial instantiations: 0
% 4.25/1.70  #Strategies tried      : 1
% 4.25/1.70  
% 4.25/1.70  Timing (in seconds)
% 4.25/1.70  ----------------------
% 4.25/1.70  Preprocessing        : 0.34
% 4.25/1.70  Parsing              : 0.18
% 4.25/1.70  CNF conversion       : 0.02
% 4.25/1.70  Main loop            : 0.61
% 4.25/1.70  Inferencing          : 0.19
% 4.25/1.70  Reduction            : 0.22
% 4.25/1.70  Demodulation         : 0.16
% 4.25/1.70  BG Simplification    : 0.03
% 4.25/1.70  Subsumption          : 0.12
% 4.25/1.70  Abstraction          : 0.03
% 4.25/1.70  MUC search           : 0.00
% 4.25/1.70  Cooper               : 0.00
% 4.25/1.70  Total                : 0.98
% 4.25/1.70  Index Insertion      : 0.00
% 4.25/1.70  Index Deletion       : 0.00
% 4.25/1.70  Index Matching       : 0.00
% 4.25/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
