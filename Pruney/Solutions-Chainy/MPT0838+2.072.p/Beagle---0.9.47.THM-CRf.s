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
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 160 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 340 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_48,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_124,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130])).

tff(c_151,plain,(
    ! [A_78] :
      ( k1_relat_1(A_78) = k1_xboole_0
      | k2_relat_1(A_78) != k1_xboole_0
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_158,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_151])).

tff(c_160,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_234,plain,(
    ! [C_95,B_96,A_97] :
      ( v5_relat_1(C_95,B_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_243,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_234])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v5_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_306,plain,(
    ! [A_117,C_118,B_119] :
      ( m1_subset_1(A_117,C_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(C_118))
      | ~ r2_hidden(A_117,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_314,plain,(
    ! [A_121,B_122,A_123] :
      ( m1_subset_1(A_121,B_122)
      | ~ r2_hidden(A_121,A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_22,c_306])).

tff(c_584,plain,(
    ! [A_164,B_165,B_166] :
      ( m1_subset_1('#skF_1'(A_164,B_165),B_166)
      | ~ r1_tarski(A_164,B_166)
      | r1_xboole_0(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_8,c_314])).

tff(c_461,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_470,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_461])).

tff(c_111,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_1'(A_68,B_69),A_68)
      | r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_46,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_116,plain,(
    ! [B_69] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_69),'#skF_3')
      | r1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_69) ) ),
    inference(resolution,[status(thm)],[c_111,c_46])).

tff(c_476,plain,(
    ! [B_69] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4'),B_69),'#skF_3')
      | r1_xboole_0(k2_relat_1('#skF_4'),B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_470,c_116])).

tff(c_621,plain,(
    ! [B_165] :
      ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
      | r1_xboole_0(k2_relat_1('#skF_4'),B_165) ) ),
    inference(resolution,[status(thm)],[c_584,c_476])).

tff(c_651,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_654,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_651])).

tff(c_661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_243,c_654])).

tff(c_667,plain,(
    ! [B_172] : r1_xboole_0(k2_relat_1('#skF_4'),B_172) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_802,plain,(
    ! [B_176] : k4_xboole_0(k2_relat_1('#skF_4'),B_176) = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_667,c_14])).

tff(c_663,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_691,plain,(
    k4_xboole_0(k2_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_663,c_12])).

tff(c_810,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_691])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_810])).

tff(c_863,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_1078,plain,(
    ! [A_214,B_215,C_216] :
      ( k1_relset_1(A_214,B_215,C_216) = k1_relat_1(C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1085,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1078])).

tff(c_1088,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_1085])).

tff(c_1090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:58:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  
% 3.19/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.51  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.19/1.51  
% 3.19/1.51  %Foreground sorts:
% 3.19/1.51  
% 3.19/1.51  
% 3.19/1.51  %Background operators:
% 3.19/1.51  
% 3.19/1.51  
% 3.19/1.51  %Foreground operators:
% 3.19/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.19/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.19/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.19/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.19/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.19/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.19/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.19/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.51  
% 3.19/1.52  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.19/1.52  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.19/1.52  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.19/1.52  tff(f_88, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 3.19/1.52  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.19/1.52  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.19/1.52  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.19/1.52  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.19/1.52  tff(f_67, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.19/1.52  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.19/1.52  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.19/1.52  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.19/1.52  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.19/1.52  tff(c_48, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.19/1.52  tff(c_32, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.19/1.52  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.19/1.52  tff(c_124, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.52  tff(c_130, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_124])).
% 3.19/1.52  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130])).
% 3.19/1.52  tff(c_151, plain, (![A_78]: (k1_relat_1(A_78)=k1_xboole_0 | k2_relat_1(A_78)!=k1_xboole_0 | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.19/1.52  tff(c_158, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_134, c_151])).
% 3.19/1.52  tff(c_160, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_158])).
% 3.19/1.52  tff(c_234, plain, (![C_95, B_96, A_97]: (v5_relat_1(C_95, B_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.19/1.52  tff(c_243, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_234])).
% 3.19/1.52  tff(c_30, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(B_22), A_21) | ~v5_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.19/1.52  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.52  tff(c_22, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.19/1.52  tff(c_306, plain, (![A_117, C_118, B_119]: (m1_subset_1(A_117, C_118) | ~m1_subset_1(B_119, k1_zfmisc_1(C_118)) | ~r2_hidden(A_117, B_119))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.52  tff(c_314, plain, (![A_121, B_122, A_123]: (m1_subset_1(A_121, B_122) | ~r2_hidden(A_121, A_123) | ~r1_tarski(A_123, B_122))), inference(resolution, [status(thm)], [c_22, c_306])).
% 3.19/1.52  tff(c_584, plain, (![A_164, B_165, B_166]: (m1_subset_1('#skF_1'(A_164, B_165), B_166) | ~r1_tarski(A_164, B_166) | r1_xboole_0(A_164, B_165))), inference(resolution, [status(thm)], [c_8, c_314])).
% 3.19/1.52  tff(c_461, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.19/1.52  tff(c_470, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_461])).
% 3.19/1.52  tff(c_111, plain, (![A_68, B_69]: (r2_hidden('#skF_1'(A_68, B_69), A_68) | r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.52  tff(c_46, plain, (![D_46]: (~r2_hidden(D_46, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_46, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.19/1.52  tff(c_116, plain, (![B_69]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_69), '#skF_3') | r1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_69))), inference(resolution, [status(thm)], [c_111, c_46])).
% 3.19/1.52  tff(c_476, plain, (![B_69]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4'), B_69), '#skF_3') | r1_xboole_0(k2_relat_1('#skF_4'), B_69))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_470, c_116])).
% 3.19/1.52  tff(c_621, plain, (![B_165]: (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | r1_xboole_0(k2_relat_1('#skF_4'), B_165))), inference(resolution, [status(thm)], [c_584, c_476])).
% 3.19/1.52  tff(c_651, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_621])).
% 3.19/1.52  tff(c_654, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_651])).
% 3.19/1.52  tff(c_661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_243, c_654])).
% 3.19/1.52  tff(c_667, plain, (![B_172]: (r1_xboole_0(k2_relat_1('#skF_4'), B_172))), inference(splitRight, [status(thm)], [c_621])).
% 3.19/1.52  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.19/1.52  tff(c_802, plain, (![B_176]: (k4_xboole_0(k2_relat_1('#skF_4'), B_176)=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_667, c_14])).
% 3.19/1.52  tff(c_663, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_621])).
% 3.19/1.52  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.52  tff(c_691, plain, (k4_xboole_0(k2_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_663, c_12])).
% 3.19/1.52  tff(c_810, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_802, c_691])).
% 3.19/1.52  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_810])).
% 3.19/1.52  tff(c_863, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_158])).
% 3.19/1.52  tff(c_1078, plain, (![A_214, B_215, C_216]: (k1_relset_1(A_214, B_215, C_216)=k1_relat_1(C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.19/1.52  tff(c_1085, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1078])).
% 3.19/1.52  tff(c_1088, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_863, c_1085])).
% 3.19/1.52  tff(c_1090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1088])).
% 3.19/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.52  
% 3.19/1.52  Inference rules
% 3.19/1.52  ----------------------
% 3.19/1.52  #Ref     : 0
% 3.19/1.52  #Sup     : 235
% 3.19/1.52  #Fact    : 0
% 3.19/1.52  #Define  : 0
% 3.19/1.52  #Split   : 6
% 3.19/1.52  #Chain   : 0
% 3.19/1.52  #Close   : 0
% 3.19/1.52  
% 3.19/1.52  Ordering : KBO
% 3.19/1.52  
% 3.19/1.52  Simplification rules
% 3.19/1.52  ----------------------
% 3.19/1.52  #Subsume      : 20
% 3.19/1.52  #Demod        : 56
% 3.19/1.52  #Tautology    : 67
% 3.19/1.52  #SimpNegUnit  : 3
% 3.19/1.52  #BackRed      : 4
% 3.19/1.52  
% 3.19/1.52  #Partial instantiations: 0
% 3.19/1.52  #Strategies tried      : 1
% 3.19/1.52  
% 3.19/1.52  Timing (in seconds)
% 3.19/1.52  ----------------------
% 3.19/1.53  Preprocessing        : 0.33
% 3.19/1.53  Parsing              : 0.18
% 3.19/1.53  CNF conversion       : 0.02
% 3.19/1.53  Main loop            : 0.42
% 3.19/1.53  Inferencing          : 0.17
% 3.19/1.53  Reduction            : 0.12
% 3.19/1.53  Demodulation         : 0.08
% 3.19/1.53  BG Simplification    : 0.02
% 3.19/1.53  Subsumption          : 0.07
% 3.19/1.53  Abstraction          : 0.02
% 3.19/1.53  MUC search           : 0.00
% 3.19/1.53  Cooper               : 0.00
% 3.19/1.53  Total                : 0.78
% 3.19/1.53  Index Insertion      : 0.00
% 3.19/1.53  Index Deletion       : 0.00
% 3.19/1.53  Index Matching       : 0.00
% 3.19/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
