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
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 386 expanded)
%              Number of leaves         :   40 ( 147 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 882 expanded)
%              Number of equality atoms :   29 ( 161 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_28,plain,(
    ! [A_32,B_33] : v1_relat_1(k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_65,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_68])).

tff(c_507,plain,(
    ! [C_136,A_137,B_138] :
      ( v4_relat_1(C_136,A_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_516,plain,(
    v4_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_507])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_566,plain,(
    ! [C_147,B_148,A_149] :
      ( r2_hidden(C_147,B_148)
      | ~ r2_hidden(C_147,A_149)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_625,plain,(
    ! [A_154,B_155,B_156] :
      ( r2_hidden('#skF_1'(A_154,B_155),B_156)
      | ~ r1_tarski(A_154,B_156)
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_566])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_642,plain,(
    ! [A_154,B_155,B_156] :
      ( m1_subset_1('#skF_1'(A_154,B_155),B_156)
      | ~ r1_tarski(A_154,B_156)
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_625,c_8])).

tff(c_700,plain,(
    ! [A_167,B_168,C_169] :
      ( k1_relset_1(A_167,B_168,C_169) = k1_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_719,plain,(
    k1_relset_1('#skF_9','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_700])).

tff(c_72,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,k1_relset_1('#skF_9','#skF_8','#skF_10'))
      | ~ m1_subset_1(D_57,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84,plain,(
    ! [B_68] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_9','#skF_8','#skF_10'),B_68),'#skF_9')
      | r1_tarski(k1_relset_1('#skF_9','#skF_8','#skF_10'),B_68) ) ),
    inference(resolution,[status(thm)],[c_72,c_44])).

tff(c_774,plain,(
    ! [B_173] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_10'),B_173),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_719,c_84])).

tff(c_779,plain,(
    ! [B_155] :
      ( ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9')
      | r1_tarski(k1_relat_1('#skF_10'),B_155) ) ),
    inference(resolution,[status(thm)],[c_642,c_774])).

tff(c_780,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_783,plain,
    ( ~ v4_relat_1('#skF_10','#skF_9')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_14,c_780])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_516,c_783])).

tff(c_788,plain,(
    ! [B_155] : r1_tarski(k1_relat_1('#skF_10'),B_155) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_570,plain,(
    ! [A_150] :
      ( k1_xboole_0 = A_150
      | r2_hidden(k4_tarski('#skF_6'(A_150),'#skF_7'(A_150)),A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [C_28,A_13,D_31] :
      ( r2_hidden(C_28,k1_relat_1(A_13))
      | ~ r2_hidden(k4_tarski(C_28,D_31),A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_587,plain,(
    ! [A_151] :
      ( r2_hidden('#skF_6'(A_151),k1_relat_1(A_151))
      | k1_xboole_0 = A_151
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_570,c_18])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_843,plain,(
    ! [A_184,B_185] :
      ( r2_hidden('#skF_6'(A_184),B_185)
      | ~ r1_tarski(k1_relat_1(A_184),B_185)
      | k1_xboole_0 = A_184
      | ~ v1_relat_1(A_184) ) ),
    inference(resolution,[status(thm)],[c_587,c_2])).

tff(c_860,plain,(
    ! [A_189,B_190] :
      ( m1_subset_1('#skF_6'(A_189),B_190)
      | ~ r1_tarski(k1_relat_1(A_189),B_190)
      | k1_xboole_0 = A_189
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_843,c_8])).

tff(c_863,plain,(
    ! [B_155] :
      ( m1_subset_1('#skF_6'('#skF_10'),B_155)
      | k1_xboole_0 = '#skF_10'
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_788,c_860])).

tff(c_876,plain,(
    ! [B_155] :
      ( m1_subset_1('#skF_6'('#skF_10'),B_155)
      | k1_xboole_0 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_863])).

tff(c_882,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_876])).

tff(c_644,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_658,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_644])).

tff(c_46,plain,(
    k2_relset_1('#skF_9','#skF_8','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_659,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_46])).

tff(c_914,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_659])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_923,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_882,c_32])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_914,c_923])).

tff(c_942,plain,(
    ! [B_155] : m1_subset_1('#skF_6'('#skF_10'),B_155) ),
    inference(splitRight,[status(thm)],[c_876])).

tff(c_584,plain,(
    ! [A_150] :
      ( r2_hidden('#skF_6'(A_150),k1_relat_1(A_150))
      | k1_xboole_0 = A_150
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_570,c_18])).

tff(c_745,plain,(
    ! [D_172] :
      ( ~ r2_hidden(D_172,k1_relat_1('#skF_10'))
      | ~ m1_subset_1(D_172,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_44])).

tff(c_757,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10'
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_584,c_745])).

tff(c_770,plain,
    ( ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_757])).

tff(c_773,plain,(
    ~ m1_subset_1('#skF_6'('#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_773])).

tff(c_964,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_966,plain,(
    k2_relat_1('#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_659])).

tff(c_975,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_964,c_32])).

tff(c_988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_966,c_975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 3.14/1.51  
% 3.14/1.51  %Foreground sorts:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Background operators:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Foreground operators:
% 3.14/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.14/1.51  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.14/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.14/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.14/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.14/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.14/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.14/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.51  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.14/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.14/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.51  
% 3.29/1.53  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.29/1.53  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.29/1.53  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.29/1.53  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.29/1.53  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.29/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.29/1.53  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.29/1.53  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.29/1.53  tff(f_67, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 3.29/1.53  tff(f_57, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.29/1.53  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.29/1.53  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.29/1.53  tff(c_28, plain, (![A_32, B_33]: (v1_relat_1(k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.53  tff(c_48, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.29/1.53  tff(c_65, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.53  tff(c_68, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_65])).
% 3.29/1.53  tff(c_71, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_68])).
% 3.29/1.53  tff(c_507, plain, (![C_136, A_137, B_138]: (v4_relat_1(C_136, A_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.29/1.53  tff(c_516, plain, (v4_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_48, c_507])).
% 3.29/1.53  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_566, plain, (![C_147, B_148, A_149]: (r2_hidden(C_147, B_148) | ~r2_hidden(C_147, A_149) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_625, plain, (![A_154, B_155, B_156]: (r2_hidden('#skF_1'(A_154, B_155), B_156) | ~r1_tarski(A_154, B_156) | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_6, c_566])).
% 3.29/1.53  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.29/1.53  tff(c_642, plain, (![A_154, B_155, B_156]: (m1_subset_1('#skF_1'(A_154, B_155), B_156) | ~r1_tarski(A_154, B_156) | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_625, c_8])).
% 3.29/1.53  tff(c_700, plain, (![A_167, B_168, C_169]: (k1_relset_1(A_167, B_168, C_169)=k1_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.29/1.53  tff(c_719, plain, (k1_relset_1('#skF_9', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_700])).
% 3.29/1.53  tff(c_72, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), A_67) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_44, plain, (![D_57]: (~r2_hidden(D_57, k1_relset_1('#skF_9', '#skF_8', '#skF_10')) | ~m1_subset_1(D_57, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.29/1.53  tff(c_84, plain, (![B_68]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_9', '#skF_8', '#skF_10'), B_68), '#skF_9') | r1_tarski(k1_relset_1('#skF_9', '#skF_8', '#skF_10'), B_68))), inference(resolution, [status(thm)], [c_72, c_44])).
% 3.29/1.53  tff(c_774, plain, (![B_173]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_10'), B_173), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_173))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_719, c_84])).
% 3.29/1.53  tff(c_779, plain, (![B_155]: (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9') | r1_tarski(k1_relat_1('#skF_10'), B_155))), inference(resolution, [status(thm)], [c_642, c_774])).
% 3.29/1.53  tff(c_780, plain, (~r1_tarski(k1_relat_1('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_779])).
% 3.29/1.53  tff(c_783, plain, (~v4_relat_1('#skF_10', '#skF_9') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_14, c_780])).
% 3.29/1.53  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_516, c_783])).
% 3.29/1.53  tff(c_788, plain, (![B_155]: (r1_tarski(k1_relat_1('#skF_10'), B_155))), inference(splitRight, [status(thm)], [c_779])).
% 3.29/1.53  tff(c_570, plain, (![A_150]: (k1_xboole_0=A_150 | r2_hidden(k4_tarski('#skF_6'(A_150), '#skF_7'(A_150)), A_150) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.53  tff(c_18, plain, (![C_28, A_13, D_31]: (r2_hidden(C_28, k1_relat_1(A_13)) | ~r2_hidden(k4_tarski(C_28, D_31), A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.29/1.53  tff(c_587, plain, (![A_151]: (r2_hidden('#skF_6'(A_151), k1_relat_1(A_151)) | k1_xboole_0=A_151 | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_570, c_18])).
% 3.29/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.29/1.53  tff(c_843, plain, (![A_184, B_185]: (r2_hidden('#skF_6'(A_184), B_185) | ~r1_tarski(k1_relat_1(A_184), B_185) | k1_xboole_0=A_184 | ~v1_relat_1(A_184))), inference(resolution, [status(thm)], [c_587, c_2])).
% 3.29/1.53  tff(c_860, plain, (![A_189, B_190]: (m1_subset_1('#skF_6'(A_189), B_190) | ~r1_tarski(k1_relat_1(A_189), B_190) | k1_xboole_0=A_189 | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_843, c_8])).
% 3.29/1.53  tff(c_863, plain, (![B_155]: (m1_subset_1('#skF_6'('#skF_10'), B_155) | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_788, c_860])).
% 3.29/1.53  tff(c_876, plain, (![B_155]: (m1_subset_1('#skF_6'('#skF_10'), B_155) | k1_xboole_0='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_863])).
% 3.29/1.53  tff(c_882, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_876])).
% 3.29/1.53  tff(c_644, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.29/1.53  tff(c_658, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_48, c_644])).
% 3.29/1.53  tff(c_46, plain, (k2_relset_1('#skF_9', '#skF_8', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.29/1.53  tff(c_659, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_658, c_46])).
% 3.29/1.53  tff(c_914, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_882, c_659])).
% 3.29/1.53  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.29/1.53  tff(c_923, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_882, c_882, c_32])).
% 3.29/1.53  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_914, c_923])).
% 3.29/1.53  tff(c_942, plain, (![B_155]: (m1_subset_1('#skF_6'('#skF_10'), B_155))), inference(splitRight, [status(thm)], [c_876])).
% 3.29/1.53  tff(c_584, plain, (![A_150]: (r2_hidden('#skF_6'(A_150), k1_relat_1(A_150)) | k1_xboole_0=A_150 | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_570, c_18])).
% 3.29/1.53  tff(c_745, plain, (![D_172]: (~r2_hidden(D_172, k1_relat_1('#skF_10')) | ~m1_subset_1(D_172, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_44])).
% 3.29/1.53  tff(c_757, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10' | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_584, c_745])).
% 3.29/1.53  tff(c_770, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_757])).
% 3.29/1.53  tff(c_773, plain, (~m1_subset_1('#skF_6'('#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_770])).
% 3.29/1.53  tff(c_963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_942, c_773])).
% 3.29/1.53  tff(c_964, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_770])).
% 3.29/1.53  tff(c_966, plain, (k2_relat_1('#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_964, c_659])).
% 3.29/1.53  tff(c_975, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_964, c_964, c_32])).
% 3.29/1.53  tff(c_988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_966, c_975])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 0
% 3.29/1.53  #Sup     : 169
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 11
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 20
% 3.29/1.53  #Demod        : 154
% 3.29/1.53  #Tautology    : 50
% 3.29/1.53  #SimpNegUnit  : 2
% 3.29/1.53  #BackRed      : 62
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.53  Preprocessing        : 0.32
% 3.29/1.53  Parsing              : 0.17
% 3.29/1.53  CNF conversion       : 0.03
% 3.29/1.53  Main loop            : 0.39
% 3.29/1.53  Inferencing          : 0.14
% 3.29/1.53  Reduction            : 0.12
% 3.29/1.53  Demodulation         : 0.08
% 3.29/1.53  BG Simplification    : 0.02
% 3.29/1.53  Subsumption          : 0.07
% 3.29/1.53  Abstraction          : 0.02
% 3.29/1.53  MUC search           : 0.00
% 3.29/1.53  Cooper               : 0.00
% 3.29/1.53  Total                : 0.74
% 3.29/1.53  Index Insertion      : 0.00
% 3.29/1.53  Index Deletion       : 0.00
% 3.29/1.53  Index Matching       : 0.00
% 3.29/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
