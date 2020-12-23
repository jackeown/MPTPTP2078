%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 140 expanded)
%              Number of leaves         :   35 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 339 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_116,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_125,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_116])).

tff(c_46,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_126,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_46])).

tff(c_568,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_1'(A_118,B_119,C_120),B_119)
      | k2_relset_1(A_118,B_119,C_120) = B_119
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_579,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_568])).

tff(c_585,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_579])).

tff(c_586,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_585])).

tff(c_56,plain,(
    ! [D_40] :
      ( r2_hidden('#skF_6'(D_40),'#skF_3')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_172,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_181,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_172])).

tff(c_589,plain,(
    ! [B_126,A_127,C_128] :
      ( k1_xboole_0 = B_126
      | k1_relset_1(A_127,B_126,C_128) = A_127
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_604,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_589])).

tff(c_611,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_181,c_604])).

tff(c_612,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_106,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_106])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,(
    ! [D_40] :
      ( k1_funct_1('#skF_5','#skF_6'(D_40)) = D_40
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_444,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(k4_tarski(A_106,k1_funct_1(C_107,A_106)),C_107)
      | ~ r2_hidden(A_106,k1_relat_1(C_107))
      | ~ v1_funct_1(C_107)
      | ~ v1_relat_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_453,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_6'(D_40),D_40),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_40),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_444])).

tff(c_458,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_6'(D_40),D_40),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_40),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_52,c_453])).

tff(c_613,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski('#skF_6'(D_40),D_40),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_40),'#skF_3')
      | ~ r2_hidden(D_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_458])).

tff(c_805,plain,(
    ! [E_150,A_151,B_152,C_153] :
      ( ~ r2_hidden(k4_tarski(E_150,'#skF_1'(A_151,B_152,C_153)),C_153)
      | k2_relset_1(A_151,B_152,C_153) = B_152
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_863,plain,(
    ! [A_161,B_162] :
      ( k2_relset_1(A_161,B_162,'#skF_5') = B_162
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_161,B_162,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_161,B_162,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_613,c_805])).

tff(c_1108,plain,(
    ! [A_190,B_191] :
      ( k2_relset_1(A_190,B_191,'#skF_5') = B_191
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ r2_hidden('#skF_1'(A_190,B_191,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_863])).

tff(c_1114,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1108])).

tff(c_1118,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_125,c_1114])).

tff(c_1120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_1118])).

tff(c_1121,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1138,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_8])).

tff(c_237,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k2_relset_1(A_89,B_90,C_91),k1_zfmisc_1(B_90))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_261,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_237])).

tff(c_267,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_261])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_271,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_267,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_273,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_271,c_2])).

tff(c_276,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_273])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:24:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  
% 3.30/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 3.30/1.51  
% 3.30/1.51  %Foreground sorts:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Background operators:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Foreground operators:
% 3.30/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.30/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.30/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.30/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.30/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.51  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.30/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.51  
% 3.30/1.53  tff(f_112, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.30/1.53  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.30/1.53  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 3.30/1.53  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.30/1.53  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.30/1.53  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.30/1.53  tff(f_47, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.30/1.53  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.30/1.53  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.30/1.53  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.30/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.30/1.53  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_116, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.30/1.53  tff(c_125, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_116])).
% 3.30/1.53  tff(c_46, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_126, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_46])).
% 3.30/1.53  tff(c_568, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_1'(A_118, B_119, C_120), B_119) | k2_relset_1(A_118, B_119, C_120)=B_119 | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.53  tff(c_579, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_568])).
% 3.30/1.53  tff(c_585, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_579])).
% 3.30/1.53  tff(c_586, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_126, c_585])).
% 3.30/1.53  tff(c_56, plain, (![D_40]: (r2_hidden('#skF_6'(D_40), '#skF_3') | ~r2_hidden(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_172, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.53  tff(c_181, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_172])).
% 3.30/1.53  tff(c_589, plain, (![B_126, A_127, C_128]: (k1_xboole_0=B_126 | k1_relset_1(A_127, B_126, C_128)=A_127 | ~v1_funct_2(C_128, A_127, B_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.30/1.53  tff(c_604, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_589])).
% 3.30/1.53  tff(c_611, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_181, c_604])).
% 3.30/1.53  tff(c_612, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_611])).
% 3.30/1.53  tff(c_106, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.53  tff(c_115, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_106])).
% 3.30/1.53  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_54, plain, (![D_40]: (k1_funct_1('#skF_5', '#skF_6'(D_40))=D_40 | ~r2_hidden(D_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.30/1.53  tff(c_444, plain, (![A_106, C_107]: (r2_hidden(k4_tarski(A_106, k1_funct_1(C_107, A_106)), C_107) | ~r2_hidden(A_106, k1_relat_1(C_107)) | ~v1_funct_1(C_107) | ~v1_relat_1(C_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.53  tff(c_453, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_6'(D_40), D_40), '#skF_5') | ~r2_hidden('#skF_6'(D_40), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_40, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_444])).
% 3.30/1.53  tff(c_458, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_6'(D_40), D_40), '#skF_5') | ~r2_hidden('#skF_6'(D_40), k1_relat_1('#skF_5')) | ~r2_hidden(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_52, c_453])).
% 3.30/1.53  tff(c_613, plain, (![D_40]: (r2_hidden(k4_tarski('#skF_6'(D_40), D_40), '#skF_5') | ~r2_hidden('#skF_6'(D_40), '#skF_3') | ~r2_hidden(D_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_458])).
% 3.30/1.53  tff(c_805, plain, (![E_150, A_151, B_152, C_153]: (~r2_hidden(k4_tarski(E_150, '#skF_1'(A_151, B_152, C_153)), C_153) | k2_relset_1(A_151, B_152, C_153)=B_152 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.53  tff(c_863, plain, (![A_161, B_162]: (k2_relset_1(A_161, B_162, '#skF_5')=B_162 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~r2_hidden('#skF_6'('#skF_1'(A_161, B_162, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_161, B_162, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_613, c_805])).
% 3.30/1.53  tff(c_1108, plain, (![A_190, B_191]: (k2_relset_1(A_190, B_191, '#skF_5')=B_191 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~r2_hidden('#skF_1'(A_190, B_191, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_863])).
% 3.30/1.53  tff(c_1114, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_48, c_1108])).
% 3.30/1.53  tff(c_1118, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_125, c_1114])).
% 3.30/1.53  tff(c_1120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_1118])).
% 3.30/1.53  tff(c_1121, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_611])).
% 3.30/1.53  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.30/1.53  tff(c_1138, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_8])).
% 3.30/1.53  tff(c_237, plain, (![A_89, B_90, C_91]: (m1_subset_1(k2_relset_1(A_89, B_90, C_91), k1_zfmisc_1(B_90)) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.30/1.53  tff(c_261, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_125, c_237])).
% 3.30/1.53  tff(c_267, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_261])).
% 3.30/1.53  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.53  tff(c_271, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_267, c_10])).
% 3.30/1.53  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.53  tff(c_273, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_271, c_2])).
% 3.30/1.53  tff(c_276, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_126, c_273])).
% 3.30/1.53  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1138, c_276])).
% 3.30/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.53  
% 3.30/1.53  Inference rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Ref     : 0
% 3.30/1.53  #Sup     : 207
% 3.30/1.53  #Fact    : 0
% 3.30/1.53  #Define  : 0
% 3.30/1.53  #Split   : 3
% 3.30/1.53  #Chain   : 0
% 3.30/1.53  #Close   : 0
% 3.30/1.53  
% 3.30/1.53  Ordering : KBO
% 3.30/1.53  
% 3.30/1.53  Simplification rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Subsume      : 12
% 3.30/1.53  #Demod        : 152
% 3.30/1.53  #Tautology    : 92
% 3.30/1.53  #SimpNegUnit  : 6
% 3.30/1.53  #BackRed      : 24
% 3.30/1.53  
% 3.30/1.53  #Partial instantiations: 0
% 3.30/1.53  #Strategies tried      : 1
% 3.30/1.53  
% 3.30/1.53  Timing (in seconds)
% 3.30/1.53  ----------------------
% 3.30/1.53  Preprocessing        : 0.35
% 3.30/1.53  Parsing              : 0.19
% 3.30/1.53  CNF conversion       : 0.02
% 3.30/1.53  Main loop            : 0.41
% 3.30/1.53  Inferencing          : 0.15
% 3.30/1.53  Reduction            : 0.13
% 3.30/1.53  Demodulation         : 0.09
% 3.30/1.53  BG Simplification    : 0.02
% 3.30/1.53  Subsumption          : 0.07
% 3.30/1.53  Abstraction          : 0.03
% 3.30/1.53  MUC search           : 0.00
% 3.42/1.53  Cooper               : 0.00
% 3.42/1.53  Total                : 0.79
% 3.42/1.53  Index Insertion      : 0.00
% 3.42/1.54  Index Deletion       : 0.00
% 3.42/1.54  Index Matching       : 0.00
% 3.42/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
