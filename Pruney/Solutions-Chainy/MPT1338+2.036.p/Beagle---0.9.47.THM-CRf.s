%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:19 EST 2020

% Result     : Theorem 11.26s
% Output     : CNFRefutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  211 (4680 expanded)
%              Number of leaves         :   59 (1634 expanded)
%              Depth                    :   18
%              Number of atoms          :  359 (14161 expanded)
%              Number of equality atoms :  127 (5265 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_205,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_49,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_169,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_134,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_181,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_96,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_24,plain,(
    ! [A_11] : v1_xboole_0('#skF_3'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [A_11] : '#skF_3'(A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_139])).

tff(c_144,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_24])).

tff(c_100,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_189,plain,(
    ! [A_67] :
      ( u1_struct_0(A_67) = k2_struct_0(A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_197,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_189])).

tff(c_196,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_96,c_189])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_212,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_196,c_90])).

tff(c_247,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_259,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_212,c_247])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_86,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11663,plain,(
    ! [A_750,B_751,C_752] :
      ( k2_relset_1(A_750,B_751,C_752) = k2_relat_1(C_752)
      | ~ m1_subset_1(C_752,k1_zfmisc_1(k2_zfmisc_1(A_750,B_751))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11691,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_212,c_11663])).

tff(c_88,plain,(
    k2_relset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_7'),'#skF_8') = k2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_198,plain,(
    k2_relset_1(u1_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_88])).

tff(c_11016,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_198])).

tff(c_11701,plain,(
    k2_struct_0('#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11691,c_11016])).

tff(c_34,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_subset_1(A_13)) = k2_subset_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_14] :
      ( r1_tarski(k1_subset_1(A_14),k3_subset_1(A_14,k1_subset_1(A_14)))
      | ~ m1_subset_1(k1_subset_1(A_14),k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_103,plain,(
    ! [A_14] :
      ( r1_tarski(k1_subset_1(A_14),k2_subset_1(A_14))
      | ~ m1_subset_1(k1_subset_1(A_14),k1_zfmisc_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_105,plain,(
    ! [A_14] :
      ( r1_tarski(k1_subset_1(A_14),A_14)
      | ~ m1_subset_1(k1_subset_1(A_14),k1_zfmisc_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_103])).

tff(c_109,plain,(
    ! [A_14] :
      ( r1_tarski(k1_xboole_0,A_14)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_105])).

tff(c_111,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_11066,plain,(
    ! [A_680] :
      ( m1_subset_1('#skF_4'(A_680),k1_zfmisc_1(u1_struct_0(A_680)))
      | ~ l1_struct_0(A_680)
      | v2_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_11074,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_11066])).

tff(c_11079,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_11074])).

tff(c_11080,plain,(
    m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_11079])).

tff(c_11021,plain,(
    ! [A_674,B_675] :
      ( r2_hidden(A_674,B_675)
      | v1_xboole_0(B_675)
      | ~ m1_subset_1(A_674,B_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( r1_tarski(C_6,A_2)
      | ~ r2_hidden(C_6,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11234,plain,(
    ! [A_711,A_712] :
      ( r1_tarski(A_711,A_712)
      | v1_xboole_0(k1_zfmisc_1(A_712))
      | ~ m1_subset_1(A_711,k1_zfmisc_1(A_712)) ) ),
    inference(resolution,[status(thm)],[c_11021,c_4])).

tff(c_11260,plain,
    ( r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_11080,c_11234])).

tff(c_11297,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_11260])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_104,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_11031,plain,(
    ! [C_676,B_677,A_678] :
      ( ~ v1_xboole_0(C_676)
      | ~ m1_subset_1(B_677,k1_zfmisc_1(C_676))
      | ~ r2_hidden(A_678,B_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11081,plain,(
    ! [A_681,A_682] :
      ( ~ v1_xboole_0(A_681)
      | ~ r2_hidden(A_682,A_681) ) ),
    inference(resolution,[status(thm)],[c_104,c_11031])).

tff(c_11092,plain,(
    ! [A_2,C_6] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_11081])).

tff(c_11309,plain,(
    ! [C_714] : ~ r1_tarski(C_714,k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_11297,c_11092])).

tff(c_11325,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_111,c_11309])).

tff(c_11326,plain,(
    r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_11260])).

tff(c_16,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_226,plain,(
    ! [A_76,B_77] :
      ( k3_tarski(A_76) != k1_xboole_0
      | ~ r2_hidden(B_77,A_76)
      | k1_xboole_0 = B_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_229,plain,(
    ! [A_2,C_6] :
      ( k3_tarski(k1_zfmisc_1(A_2)) != k1_xboole_0
      | k1_xboole_0 = C_6
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_226])).

tff(c_234,plain,(
    ! [A_2,C_6] :
      ( k1_xboole_0 != A_2
      | k1_xboole_0 = C_6
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_229])).

tff(c_11355,plain,
    ( k2_struct_0('#skF_7') != k1_xboole_0
    | '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11326,c_234])).

tff(c_11428,plain,(
    k2_struct_0('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_11355])).

tff(c_11710,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_11428])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_199,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_92])).

tff(c_210,plain,(
    v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_199])).

tff(c_11719,plain,(
    v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_210])).

tff(c_11559,plain,(
    ! [A_739,B_740,C_741] :
      ( k1_relset_1(A_739,B_740,C_741) = k1_relat_1(C_741)
      | ~ m1_subset_1(C_741,k1_zfmisc_1(k2_zfmisc_1(A_739,B_740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_11587,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_212,c_11559])).

tff(c_11708,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_11587])).

tff(c_11718,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_212])).

tff(c_16308,plain,(
    ! [B_1032,A_1033,C_1034] :
      ( k1_xboole_0 = B_1032
      | k1_relset_1(A_1033,B_1032,C_1034) = A_1033
      | ~ v1_funct_2(C_1034,A_1033,B_1032)
      | ~ m1_subset_1(C_1034,k1_zfmisc_1(k2_zfmisc_1(A_1033,B_1032))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16319,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_struct_0('#skF_6')
    | ~ v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11718,c_16308])).

tff(c_16344,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11719,c_11708,c_16319])).

tff(c_16345,plain,(
    k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_11710,c_16344])).

tff(c_16367,plain,(
    v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16345,c_11719])).

tff(c_11706,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_11691])).

tff(c_16363,plain,(
    k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16345,c_11706])).

tff(c_16365,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16345,c_11718])).

tff(c_16964,plain,(
    ! [C_1073,B_1074,A_1075] :
      ( m1_subset_1(k2_funct_1(C_1073),k1_zfmisc_1(k2_zfmisc_1(B_1074,A_1075)))
      | k2_relset_1(A_1075,B_1074,C_1073) != B_1074
      | ~ v2_funct_1(C_1073)
      | ~ m1_subset_1(C_1073,k1_zfmisc_1(k2_zfmisc_1(A_1075,B_1074)))
      | ~ v1_funct_2(C_1073,A_1075,B_1074)
      | ~ v1_funct_1(C_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relset_1(A_32,B_33,C_34) = k2_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20398,plain,(
    ! [B_1208,A_1209,C_1210] :
      ( k2_relset_1(B_1208,A_1209,k2_funct_1(C_1210)) = k2_relat_1(k2_funct_1(C_1210))
      | k2_relset_1(A_1209,B_1208,C_1210) != B_1208
      | ~ v2_funct_1(C_1210)
      | ~ m1_subset_1(C_1210,k1_zfmisc_1(k2_zfmisc_1(A_1209,B_1208)))
      | ~ v1_funct_2(C_1210,A_1209,B_1208)
      | ~ v1_funct_1(C_1210) ) ),
    inference(resolution,[status(thm)],[c_16964,c_50])).

tff(c_20432,plain,
    ( k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k2_relat_1(k2_funct_1('#skF_8'))
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16365,c_20398])).

tff(c_20471,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k2_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16367,c_86,c_16363,c_20432])).

tff(c_16750,plain,(
    ! [A_1062,B_1063,C_1064] :
      ( k2_tops_2(A_1062,B_1063,C_1064) = k2_funct_1(C_1064)
      | ~ v2_funct_1(C_1064)
      | k2_relset_1(A_1062,B_1063,C_1064) != B_1063
      | ~ m1_subset_1(C_1064,k1_zfmisc_1(k2_zfmisc_1(A_1062,B_1063)))
      | ~ v1_funct_2(C_1064,A_1062,B_1063)
      | ~ v1_funct_1(C_1064) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_16753,plain,
    ( k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16365,c_16750])).

tff(c_16784,plain,(
    k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_16367,c_16363,c_86,c_16753])).

tff(c_44,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_861,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_889,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_212,c_861])).

tff(c_275,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_198])).

tff(c_899,plain,(
    k2_struct_0('#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_275])).

tff(c_265,plain,(
    ! [A_85,B_86] :
      ( r2_hidden(A_85,B_86)
      | v1_xboole_0(B_86)
      | ~ m1_subset_1(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_520,plain,(
    ! [A_124,A_125] :
      ( r1_tarski(A_124,A_125)
      | v1_xboole_0(k1_zfmisc_1(A_125))
      | ~ m1_subset_1(A_124,k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_265,c_4])).

tff(c_552,plain,(
    ! [A_126] :
      ( r1_tarski(A_126,A_126)
      | v1_xboole_0(k1_zfmisc_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_104,c_520])).

tff(c_280,plain,(
    ! [C_87,B_88,A_89] :
      ( ~ v1_xboole_0(C_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(C_87))
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_325,plain,(
    ! [A_94,A_95] :
      ( ~ v1_xboole_0(A_94)
      | ~ r2_hidden(A_95,A_94) ) ),
    inference(resolution,[status(thm)],[c_104,c_280])).

tff(c_336,plain,(
    ! [A_2,C_6] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_325])).

tff(c_602,plain,(
    ! [C_128,A_129] :
      ( ~ r1_tarski(C_128,A_129)
      | r1_tarski(A_129,A_129) ) ),
    inference(resolution,[status(thm)],[c_552,c_336])).

tff(c_614,plain,(
    ! [A_14] : r1_tarski(A_14,A_14) ),
    inference(resolution,[status(thm)],[c_111,c_602])).

tff(c_388,plain,(
    ! [A_104] :
      ( m1_subset_1('#skF_4'(A_104),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_398,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_388])).

tff(c_404,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_398])).

tff(c_405,plain,(
    m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_404])).

tff(c_543,plain,
    ( r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_405,c_520])).

tff(c_653,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_543])).

tff(c_665,plain,(
    ! [C_133] : ~ r1_tarski(C_133,k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_653,c_336])).

tff(c_677,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_614,c_665])).

tff(c_678,plain,(
    r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_543])).

tff(c_687,plain,
    ( k2_struct_0('#skF_7') != k1_xboole_0
    | '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_678,c_234])).

tff(c_688,plain,(
    k2_struct_0('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_910,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_688])).

tff(c_919,plain,(
    v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_210])).

tff(c_766,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_794,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_212,c_766])).

tff(c_908,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_794])).

tff(c_918,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_212])).

tff(c_5746,plain,(
    ! [B_465,A_466,C_467] :
      ( k1_xboole_0 = B_465
      | k1_relset_1(A_466,B_465,C_467) = A_466
      | ~ v1_funct_2(C_467,A_466,B_465)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(A_466,B_465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5757,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_struct_0('#skF_6')
    | ~ v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_918,c_5746])).

tff(c_5782,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_908,c_5757])).

tff(c_5783,plain,(
    k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_910,c_5782])).

tff(c_5804,plain,(
    v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5783,c_919])).

tff(c_904,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_889])).

tff(c_5797,plain,(
    k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5783,c_904])).

tff(c_5798,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5783,c_918])).

tff(c_6241,plain,(
    ! [C_490,B_491,A_492] :
      ( m1_subset_1(k2_funct_1(C_490),k1_zfmisc_1(k2_zfmisc_1(B_491,A_492)))
      | k2_relset_1(A_492,B_491,C_490) != B_491
      | ~ v2_funct_1(C_490)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_492,B_491)))
      | ~ v1_funct_2(C_490,A_492,B_491)
      | ~ v1_funct_1(C_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10895,plain,(
    ! [B_671,A_672,C_673] :
      ( k1_relset_1(B_671,A_672,k2_funct_1(C_673)) = k1_relat_1(k2_funct_1(C_673))
      | k2_relset_1(A_672,B_671,C_673) != B_671
      | ~ v2_funct_1(C_673)
      | ~ m1_subset_1(C_673,k1_zfmisc_1(k2_zfmisc_1(A_672,B_671)))
      | ~ v1_funct_2(C_673,A_672,B_671)
      | ~ v1_funct_1(C_673) ) ),
    inference(resolution,[status(thm)],[c_6241,c_48])).

tff(c_10929,plain,
    ( k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8'))
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5798,c_10895])).

tff(c_10968,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_5804,c_86,c_5797,c_10929])).

tff(c_6043,plain,(
    ! [A_480,B_481,C_482] :
      ( k2_tops_2(A_480,B_481,C_482) = k2_funct_1(C_482)
      | ~ v2_funct_1(C_482)
      | k2_relset_1(A_480,B_481,C_482) != B_481
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481)))
      | ~ v1_funct_2(C_482,A_480,B_481)
      | ~ v1_funct_1(C_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6046,plain,
    ( k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5798,c_6043])).

tff(c_6077,plain,(
    k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_5804,c_5797,c_86,c_6046])).

tff(c_84,plain,
    ( k2_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),k2_tops_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_6')
    | k1_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),k2_tops_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_263,plain,
    ( k2_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_6')
    | k1_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_197,c_196,c_196,c_197,c_197,c_196,c_196,c_84])).

tff(c_264,plain,(
    k1_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_909,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_899,c_899,c_264])).

tff(c_5795,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5783,c_5783,c_909])).

tff(c_6092,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6077,c_5795])).

tff(c_10979,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10968,c_6092])).

tff(c_10986,plain,
    ( ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10979])).

tff(c_10990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_94,c_86,c_10986])).

tff(c_10991,plain,(
    '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_72,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0('#skF_4'(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_11004,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10991,c_72])).

tff(c_11011,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_144,c_11004])).

tff(c_11013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_11011])).

tff(c_11014,plain,(
    k2_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_11709,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8')) != k2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_11701,c_11014])).

tff(c_16358,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8')) != k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16345,c_16345,c_16345,c_11709])).

tff(c_16796,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) != k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16784,c_16358])).

tff(c_20482,plain,(
    k2_relat_1(k2_funct_1('#skF_8')) != k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20471,c_16796])).

tff(c_20489,plain,
    ( ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_20482])).

tff(c_20493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_94,c_86,c_20489])).

tff(c_20494,plain,(
    '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11355])).

tff(c_20507,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_20494,c_72])).

tff(c_20514,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_144,c_20507])).

tff(c_20516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_20514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:19:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.26/4.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/4.41  
% 11.26/4.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/4.41  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 11.26/4.41  
% 11.26/4.41  %Foreground sorts:
% 11.26/4.41  
% 11.26/4.41  
% 11.26/4.41  %Background operators:
% 11.26/4.41  
% 11.26/4.41  
% 11.26/4.41  %Foreground operators:
% 11.26/4.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.26/4.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.26/4.41  tff('#skF_5', type, '#skF_5': $i > $i).
% 11.26/4.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.26/4.41  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.26/4.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.26/4.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.26/4.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.26/4.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.26/4.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.26/4.41  tff('#skF_7', type, '#skF_7': $i).
% 11.26/4.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.26/4.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.26/4.41  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 11.26/4.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.26/4.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.26/4.41  tff('#skF_6', type, '#skF_6': $i).
% 11.26/4.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.26/4.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.26/4.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.26/4.41  tff('#skF_8', type, '#skF_8': $i).
% 11.26/4.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.26/4.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.26/4.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.26/4.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.26/4.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.26/4.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.26/4.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.26/4.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 11.26/4.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.26/4.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.26/4.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.26/4.41  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.26/4.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.26/4.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.26/4.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.26/4.41  
% 11.43/4.44  tff(f_205, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 11.43/4.44  tff(f_49, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 11.43/4.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 11.43/4.44  tff(f_138, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 11.43/4.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.43/4.44  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.43/4.44  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.43/4.44  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.43/4.44  tff(f_40, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 11.43/4.44  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 11.43/4.44  tff(f_51, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 11.43/4.44  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 11.43/4.44  tff(f_149, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_struct_0)).
% 11.43/4.44  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.43/4.44  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.43/4.44  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 11.43/4.44  tff(f_78, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 11.43/4.44  tff(f_38, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 11.43/4.44  tff(f_169, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 11.43/4.44  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.43/4.44  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.43/4.44  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.43/4.44  tff(f_181, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 11.43/4.44  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_96, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_24, plain, (![A_11]: (v1_xboole_0('#skF_3'(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.43/4.44  tff(c_139, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.43/4.44  tff(c_143, plain, (![A_11]: ('#skF_3'(A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_139])).
% 11.43/4.44  tff(c_144, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_24])).
% 11.43/4.44  tff(c_100, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_189, plain, (![A_67]: (u1_struct_0(A_67)=k2_struct_0(A_67) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.43/4.44  tff(c_197, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_100, c_189])).
% 11.43/4.44  tff(c_196, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_96, c_189])).
% 11.43/4.44  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_212, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_196, c_90])).
% 11.43/4.44  tff(c_247, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.43/4.44  tff(c_259, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_212, c_247])).
% 11.43/4.44  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_86, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_42, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.43/4.44  tff(c_11663, plain, (![A_750, B_751, C_752]: (k2_relset_1(A_750, B_751, C_752)=k2_relat_1(C_752) | ~m1_subset_1(C_752, k1_zfmisc_1(k2_zfmisc_1(A_750, B_751))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.43/4.44  tff(c_11691, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_212, c_11663])).
% 11.43/4.44  tff(c_88, plain, (k2_relset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'), '#skF_8')=k2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_198, plain, (k2_relset_1(u1_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_88])).
% 11.43/4.44  tff(c_11016, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_198])).
% 11.43/4.44  tff(c_11701, plain, (k2_struct_0('#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11691, c_11016])).
% 11.43/4.44  tff(c_34, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.43/4.44  tff(c_18, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.43/4.44  tff(c_20, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.43/4.44  tff(c_28, plain, (![A_13]: (k3_subset_1(A_13, k1_subset_1(A_13))=k2_subset_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.43/4.44  tff(c_30, plain, (![A_14]: (r1_tarski(k1_subset_1(A_14), k3_subset_1(A_14, k1_subset_1(A_14))) | ~m1_subset_1(k1_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.43/4.44  tff(c_103, plain, (![A_14]: (r1_tarski(k1_subset_1(A_14), k2_subset_1(A_14)) | ~m1_subset_1(k1_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 11.43/4.44  tff(c_105, plain, (![A_14]: (r1_tarski(k1_subset_1(A_14), A_14) | ~m1_subset_1(k1_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_103])).
% 11.43/4.44  tff(c_109, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_105])).
% 11.43/4.44  tff(c_111, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_109])).
% 11.43/4.44  tff(c_11066, plain, (![A_680]: (m1_subset_1('#skF_4'(A_680), k1_zfmisc_1(u1_struct_0(A_680))) | ~l1_struct_0(A_680) | v2_struct_0(A_680))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.43/4.44  tff(c_11074, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_196, c_11066])).
% 11.43/4.44  tff(c_11079, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_11074])).
% 11.43/4.44  tff(c_11080, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_98, c_11079])).
% 11.43/4.44  tff(c_11021, plain, (![A_674, B_675]: (r2_hidden(A_674, B_675) | v1_xboole_0(B_675) | ~m1_subset_1(A_674, B_675))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.44  tff(c_4, plain, (![C_6, A_2]: (r1_tarski(C_6, A_2) | ~r2_hidden(C_6, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.43/4.44  tff(c_11234, plain, (![A_711, A_712]: (r1_tarski(A_711, A_712) | v1_xboole_0(k1_zfmisc_1(A_712)) | ~m1_subset_1(A_711, k1_zfmisc_1(A_712)))), inference(resolution, [status(thm)], [c_11021, c_4])).
% 11.43/4.44  tff(c_11260, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_11080, c_11234])).
% 11.43/4.44  tff(c_11297, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_11260])).
% 11.43/4.44  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.43/4.44  tff(c_22, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.43/4.44  tff(c_104, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 11.43/4.44  tff(c_11031, plain, (![C_676, B_677, A_678]: (~v1_xboole_0(C_676) | ~m1_subset_1(B_677, k1_zfmisc_1(C_676)) | ~r2_hidden(A_678, B_677))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.43/4.44  tff(c_11081, plain, (![A_681, A_682]: (~v1_xboole_0(A_681) | ~r2_hidden(A_682, A_681))), inference(resolution, [status(thm)], [c_104, c_11031])).
% 11.43/4.44  tff(c_11092, plain, (![A_2, C_6]: (~v1_xboole_0(k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_11081])).
% 11.43/4.44  tff(c_11309, plain, (![C_714]: (~r1_tarski(C_714, k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_11297, c_11092])).
% 11.43/4.44  tff(c_11325, plain, $false, inference(resolution, [status(thm)], [c_111, c_11309])).
% 11.43/4.44  tff(c_11326, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_11260])).
% 11.43/4.44  tff(c_16, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.43/4.44  tff(c_226, plain, (![A_76, B_77]: (k3_tarski(A_76)!=k1_xboole_0 | ~r2_hidden(B_77, A_76) | k1_xboole_0=B_77)), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.43/4.44  tff(c_229, plain, (![A_2, C_6]: (k3_tarski(k1_zfmisc_1(A_2))!=k1_xboole_0 | k1_xboole_0=C_6 | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_226])).
% 11.43/4.44  tff(c_234, plain, (![A_2, C_6]: (k1_xboole_0!=A_2 | k1_xboole_0=C_6 | ~r1_tarski(C_6, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_229])).
% 11.43/4.44  tff(c_11355, plain, (k2_struct_0('#skF_7')!=k1_xboole_0 | '#skF_4'('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_11326, c_234])).
% 11.43/4.44  tff(c_11428, plain, (k2_struct_0('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_11355])).
% 11.43/4.44  tff(c_11710, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_11428])).
% 11.43/4.44  tff(c_92, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_199, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_92])).
% 11.43/4.44  tff(c_210, plain, (v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_199])).
% 11.43/4.44  tff(c_11719, plain, (v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_210])).
% 11.43/4.44  tff(c_11559, plain, (![A_739, B_740, C_741]: (k1_relset_1(A_739, B_740, C_741)=k1_relat_1(C_741) | ~m1_subset_1(C_741, k1_zfmisc_1(k2_zfmisc_1(A_739, B_740))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.43/4.44  tff(c_11587, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_212, c_11559])).
% 11.43/4.44  tff(c_11708, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_11587])).
% 11.43/4.44  tff(c_11718, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_212])).
% 11.43/4.44  tff(c_16308, plain, (![B_1032, A_1033, C_1034]: (k1_xboole_0=B_1032 | k1_relset_1(A_1033, B_1032, C_1034)=A_1033 | ~v1_funct_2(C_1034, A_1033, B_1032) | ~m1_subset_1(C_1034, k1_zfmisc_1(k2_zfmisc_1(A_1033, B_1032))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.43/4.44  tff(c_16319, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_struct_0('#skF_6') | ~v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_11718, c_16308])).
% 11.43/4.44  tff(c_16344, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11719, c_11708, c_16319])).
% 11.43/4.44  tff(c_16345, plain, (k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_11710, c_16344])).
% 11.43/4.44  tff(c_16367, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_16345, c_11719])).
% 11.43/4.44  tff(c_11706, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_11691])).
% 11.43/4.44  tff(c_16363, plain, (k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16345, c_11706])).
% 11.43/4.44  tff(c_16365, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_16345, c_11718])).
% 11.43/4.44  tff(c_16964, plain, (![C_1073, B_1074, A_1075]: (m1_subset_1(k2_funct_1(C_1073), k1_zfmisc_1(k2_zfmisc_1(B_1074, A_1075))) | k2_relset_1(A_1075, B_1074, C_1073)!=B_1074 | ~v2_funct_1(C_1073) | ~m1_subset_1(C_1073, k1_zfmisc_1(k2_zfmisc_1(A_1075, B_1074))) | ~v1_funct_2(C_1073, A_1075, B_1074) | ~v1_funct_1(C_1073))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.43/4.44  tff(c_50, plain, (![A_32, B_33, C_34]: (k2_relset_1(A_32, B_33, C_34)=k2_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.43/4.44  tff(c_20398, plain, (![B_1208, A_1209, C_1210]: (k2_relset_1(B_1208, A_1209, k2_funct_1(C_1210))=k2_relat_1(k2_funct_1(C_1210)) | k2_relset_1(A_1209, B_1208, C_1210)!=B_1208 | ~v2_funct_1(C_1210) | ~m1_subset_1(C_1210, k1_zfmisc_1(k2_zfmisc_1(A_1209, B_1208))) | ~v1_funct_2(C_1210, A_1209, B_1208) | ~v1_funct_1(C_1210))), inference(resolution, [status(thm)], [c_16964, c_50])).
% 11.43/4.44  tff(c_20432, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k2_relat_1(k2_funct_1('#skF_8')) | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v2_funct_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_16365, c_20398])).
% 11.43/4.44  tff(c_20471, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k2_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_16367, c_86, c_16363, c_20432])).
% 11.43/4.44  tff(c_16750, plain, (![A_1062, B_1063, C_1064]: (k2_tops_2(A_1062, B_1063, C_1064)=k2_funct_1(C_1064) | ~v2_funct_1(C_1064) | k2_relset_1(A_1062, B_1063, C_1064)!=B_1063 | ~m1_subset_1(C_1064, k1_zfmisc_1(k2_zfmisc_1(A_1062, B_1063))) | ~v1_funct_2(C_1064, A_1062, B_1063) | ~v1_funct_1(C_1064))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.43/4.44  tff(c_16753, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8') | ~v2_funct_1('#skF_8') | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_16365, c_16750])).
% 11.43/4.44  tff(c_16784, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_16367, c_16363, c_86, c_16753])).
% 11.43/4.44  tff(c_44, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.43/4.44  tff(c_861, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.43/4.44  tff(c_889, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_212, c_861])).
% 11.43/4.44  tff(c_275, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_198])).
% 11.43/4.44  tff(c_899, plain, (k2_struct_0('#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_889, c_275])).
% 11.43/4.44  tff(c_265, plain, (![A_85, B_86]: (r2_hidden(A_85, B_86) | v1_xboole_0(B_86) | ~m1_subset_1(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.43/4.44  tff(c_520, plain, (![A_124, A_125]: (r1_tarski(A_124, A_125) | v1_xboole_0(k1_zfmisc_1(A_125)) | ~m1_subset_1(A_124, k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_265, c_4])).
% 11.43/4.44  tff(c_552, plain, (![A_126]: (r1_tarski(A_126, A_126) | v1_xboole_0(k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_104, c_520])).
% 11.43/4.44  tff(c_280, plain, (![C_87, B_88, A_89]: (~v1_xboole_0(C_87) | ~m1_subset_1(B_88, k1_zfmisc_1(C_87)) | ~r2_hidden(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.43/4.44  tff(c_325, plain, (![A_94, A_95]: (~v1_xboole_0(A_94) | ~r2_hidden(A_95, A_94))), inference(resolution, [status(thm)], [c_104, c_280])).
% 11.43/4.44  tff(c_336, plain, (![A_2, C_6]: (~v1_xboole_0(k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_325])).
% 11.43/4.44  tff(c_602, plain, (![C_128, A_129]: (~r1_tarski(C_128, A_129) | r1_tarski(A_129, A_129))), inference(resolution, [status(thm)], [c_552, c_336])).
% 11.43/4.44  tff(c_614, plain, (![A_14]: (r1_tarski(A_14, A_14))), inference(resolution, [status(thm)], [c_111, c_602])).
% 11.43/4.44  tff(c_388, plain, (![A_104]: (m1_subset_1('#skF_4'(A_104), k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.43/4.44  tff(c_398, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_196, c_388])).
% 11.43/4.44  tff(c_404, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_398])).
% 11.43/4.44  tff(c_405, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_98, c_404])).
% 11.43/4.44  tff(c_543, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_405, c_520])).
% 11.43/4.44  tff(c_653, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_543])).
% 11.43/4.44  tff(c_665, plain, (![C_133]: (~r1_tarski(C_133, k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_653, c_336])).
% 11.43/4.44  tff(c_677, plain, $false, inference(resolution, [status(thm)], [c_614, c_665])).
% 11.43/4.44  tff(c_678, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_543])).
% 11.43/4.44  tff(c_687, plain, (k2_struct_0('#skF_7')!=k1_xboole_0 | '#skF_4'('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_678, c_234])).
% 11.43/4.44  tff(c_688, plain, (k2_struct_0('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_687])).
% 11.43/4.44  tff(c_910, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_899, c_688])).
% 11.43/4.44  tff(c_919, plain, (v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_210])).
% 11.43/4.44  tff(c_766, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.43/4.44  tff(c_794, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_212, c_766])).
% 11.43/4.44  tff(c_908, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_794])).
% 11.43/4.44  tff(c_918, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_212])).
% 11.43/4.44  tff(c_5746, plain, (![B_465, A_466, C_467]: (k1_xboole_0=B_465 | k1_relset_1(A_466, B_465, C_467)=A_466 | ~v1_funct_2(C_467, A_466, B_465) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(A_466, B_465))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.43/4.44  tff(c_5757, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_struct_0('#skF_6') | ~v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_918, c_5746])).
% 11.43/4.44  tff(c_5782, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_919, c_908, c_5757])).
% 11.43/4.44  tff(c_5783, plain, (k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_910, c_5782])).
% 11.43/4.44  tff(c_5804, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5783, c_919])).
% 11.43/4.44  tff(c_904, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_889])).
% 11.43/4.44  tff(c_5797, plain, (k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5783, c_904])).
% 11.43/4.44  tff(c_5798, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_5783, c_918])).
% 11.43/4.44  tff(c_6241, plain, (![C_490, B_491, A_492]: (m1_subset_1(k2_funct_1(C_490), k1_zfmisc_1(k2_zfmisc_1(B_491, A_492))) | k2_relset_1(A_492, B_491, C_490)!=B_491 | ~v2_funct_1(C_490) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_492, B_491))) | ~v1_funct_2(C_490, A_492, B_491) | ~v1_funct_1(C_490))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.43/4.44  tff(c_48, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.43/4.44  tff(c_10895, plain, (![B_671, A_672, C_673]: (k1_relset_1(B_671, A_672, k2_funct_1(C_673))=k1_relat_1(k2_funct_1(C_673)) | k2_relset_1(A_672, B_671, C_673)!=B_671 | ~v2_funct_1(C_673) | ~m1_subset_1(C_673, k1_zfmisc_1(k2_zfmisc_1(A_672, B_671))) | ~v1_funct_2(C_673, A_672, B_671) | ~v1_funct_1(C_673))), inference(resolution, [status(thm)], [c_6241, c_48])).
% 11.43/4.44  tff(c_10929, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8')) | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v2_funct_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_5798, c_10895])).
% 11.43/4.44  tff(c_10968, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_5804, c_86, c_5797, c_10929])).
% 11.43/4.44  tff(c_6043, plain, (![A_480, B_481, C_482]: (k2_tops_2(A_480, B_481, C_482)=k2_funct_1(C_482) | ~v2_funct_1(C_482) | k2_relset_1(A_480, B_481, C_482)!=B_481 | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))) | ~v1_funct_2(C_482, A_480, B_481) | ~v1_funct_1(C_482))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.43/4.44  tff(c_6046, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8') | ~v2_funct_1('#skF_8') | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_5798, c_6043])).
% 11.43/4.44  tff(c_6077, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_5804, c_5797, c_86, c_6046])).
% 11.43/4.44  tff(c_84, plain, (k2_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), k2_tops_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_6') | k1_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), k2_tops_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_205])).
% 11.43/4.44  tff(c_263, plain, (k2_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_6') | k1_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_197, c_196, c_196, c_197, c_197, c_196, c_196, c_84])).
% 11.43/4.44  tff(c_264, plain, (k1_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_263])).
% 11.43/4.44  tff(c_909, plain, (k1_relset_1(k2_relat_1('#skF_8'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_899, c_899, c_264])).
% 11.43/4.44  tff(c_5795, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5783, c_5783, c_909])).
% 11.43/4.44  tff(c_6092, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6077, c_5795])).
% 11.43/4.44  tff(c_10979, plain, (k1_relat_1(k2_funct_1('#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10968, c_6092])).
% 11.43/4.44  tff(c_10986, plain, (~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_44, c_10979])).
% 11.43/4.44  tff(c_10990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_259, c_94, c_86, c_10986])).
% 11.43/4.44  tff(c_10991, plain, ('#skF_4'('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_687])).
% 11.43/4.44  tff(c_72, plain, (![A_42]: (~v1_xboole_0('#skF_4'(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.43/4.44  tff(c_11004, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10991, c_72])).
% 11.43/4.44  tff(c_11011, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_144, c_11004])).
% 11.43/4.44  tff(c_11013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_11011])).
% 11.43/4.44  tff(c_11014, plain, (k2_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_263])).
% 11.43/4.44  tff(c_11709, plain, (k2_relset_1(k2_relat_1('#skF_8'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8'))!=k2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_11701, c_11014])).
% 11.43/4.44  tff(c_16358, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8'))!=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16345, c_16345, c_16345, c_11709])).
% 11.43/4.44  tff(c_16796, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))!=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16784, c_16358])).
% 11.43/4.44  tff(c_20482, plain, (k2_relat_1(k2_funct_1('#skF_8'))!=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20471, c_16796])).
% 11.43/4.44  tff(c_20489, plain, (~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_42, c_20482])).
% 11.43/4.44  tff(c_20493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_259, c_94, c_86, c_20489])).
% 11.43/4.44  tff(c_20494, plain, ('#skF_4'('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_11355])).
% 11.43/4.44  tff(c_20507, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_20494, c_72])).
% 11.43/4.44  tff(c_20514, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_144, c_20507])).
% 11.43/4.44  tff(c_20516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_20514])).
% 11.43/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.43/4.44  
% 11.43/4.44  Inference rules
% 11.43/4.44  ----------------------
% 11.43/4.44  #Ref     : 0
% 11.43/4.44  #Sup     : 4344
% 11.43/4.44  #Fact    : 0
% 11.43/4.44  #Define  : 0
% 11.43/4.44  #Split   : 45
% 11.43/4.44  #Chain   : 0
% 11.43/4.44  #Close   : 0
% 11.43/4.44  
% 11.43/4.44  Ordering : KBO
% 11.43/4.44  
% 11.43/4.44  Simplification rules
% 11.43/4.44  ----------------------
% 11.43/4.44  #Subsume      : 737
% 11.43/4.44  #Demod        : 1432
% 11.43/4.44  #Tautology    : 897
% 11.43/4.44  #SimpNegUnit  : 192
% 11.43/4.44  #BackRed      : 200
% 11.43/4.44  
% 11.43/4.44  #Partial instantiations: 0
% 11.43/4.44  #Strategies tried      : 1
% 11.43/4.44  
% 11.43/4.44  Timing (in seconds)
% 11.43/4.44  ----------------------
% 11.43/4.44  Preprocessing        : 0.38
% 11.43/4.44  Parsing              : 0.20
% 11.43/4.44  CNF conversion       : 0.03
% 11.43/4.44  Main loop            : 3.26
% 11.43/4.44  Inferencing          : 0.92
% 11.43/4.44  Reduction            : 1.00
% 11.43/4.44  Demodulation         : 0.69
% 11.43/4.44  BG Simplification    : 0.12
% 11.43/4.44  Subsumption          : 0.95
% 11.43/4.44  Abstraction          : 0.16
% 11.43/4.44  MUC search           : 0.00
% 11.43/4.44  Cooper               : 0.00
% 11.43/4.44  Total                : 3.71
% 11.43/4.44  Index Insertion      : 0.00
% 11.43/4.44  Index Deletion       : 0.00
% 11.43/4.44  Index Matching       : 0.00
% 11.43/4.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
