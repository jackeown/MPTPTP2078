%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:20 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 393 expanded)
%              Number of leaves         :   34 ( 148 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 (1075 expanded)
%              Number of equality atoms :   36 ( 197 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_61,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_61])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_79,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(B_57) = A_58
      | ~ v1_partfun1(B_57,A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_82,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_79])).

tff(c_85,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_82])).

tff(c_86,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_87,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_partfun1(C_59,A_60)
      | ~ v1_funct_2(C_59,A_60,B_61)
      | ~ v1_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | v1_xboole_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_93,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_90])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_86,c_93])).

tff(c_96,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_34,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    ! [B_64] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_64),B_64),k1_relat_1(B_64))
      | k6_partfun1(k1_relat_1(B_64)) = B_64
      | ~ v1_funct_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_115,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),k1_relat_1('#skF_4'))
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_109])).

tff(c_121,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_96,c_96,c_115])).

tff(c_132,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_36,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4',k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_133,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_36])).

tff(c_28,plain,(
    ! [D_28,A_20,B_21,C_22] :
      ( k1_funct_1(D_28,'#skF_2'(A_20,B_21,C_22,D_28)) != k1_funct_1(C_22,'#skF_2'(A_20,B_21,C_22,D_28))
      | r2_funct_2(A_20,B_21,C_22,D_28)
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(D_28,A_20,B_21)
      | ~ v1_funct_1(D_28)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_232,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_funct_2(A_94,B_95,C_96,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_28])).

tff(c_234,plain,
    ( r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_232])).

tff(c_237,plain,(
    r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_237])).

tff(c_241,plain,(
    k6_partfun1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_4,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_269,plain,(
    ! [B_98] :
      ( k1_funct_1(B_98,'#skF_1'(k1_relat_1(B_98),B_98)) != '#skF_1'(k1_relat_1(B_98),B_98)
      | k6_partfun1(k1_relat_1(B_98)) = B_98
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_272,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'(k1_relat_1('#skF_4'),'#skF_4')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_269])).

tff(c_274,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'('#skF_3','#skF_4')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_44,c_96,c_96,c_272])).

tff(c_275,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_274])).

tff(c_240,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_245,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_2])).

tff(c_38,plain,(
    ! [C_41] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',C_41) = C_41
      | ~ m1_subset_1(C_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_249,plain,(
    k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_245,c_38])).

tff(c_276,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k3_funct_2(A_99,B_100,C_101,D_102) = k1_funct_1(C_101,D_102)
      | ~ m1_subset_1(D_102,A_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_101,A_99,B_100)
      | ~ v1_funct_1(C_101)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_280,plain,(
    ! [B_100,C_101] :
      ( k3_funct_2('#skF_3',B_100,C_101,'#skF_1'('#skF_3','#skF_4')) = k1_funct_1(C_101,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_100)))
      | ~ v1_funct_2(C_101,'#skF_3',B_100)
      | ~ v1_funct_1(C_101)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_245,c_276])).

tff(c_302,plain,(
    ! [B_108,C_109] :
      ( k3_funct_2('#skF_3',B_108,C_109,'#skF_1'('#skF_3','#skF_4')) = k1_funct_1(C_109,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_108)))
      | ~ v1_funct_2(C_109,'#skF_3',B_108)
      | ~ v1_funct_1(C_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_280])).

tff(c_305,plain,
    ( k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_302])).

tff(c_308,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_249,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n013.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:50:24 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.27  
% 2.45/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.27  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.45/1.27  
% 2.45/1.27  %Foreground sorts:
% 2.45/1.27  
% 2.45/1.27  
% 2.45/1.27  %Background operators:
% 2.45/1.27  
% 2.45/1.27  
% 2.45/1.27  %Foreground operators:
% 2.45/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.45/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.45/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.45/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.45/1.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.45/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.45/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.27  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.45/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.27  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.45/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.27  
% 2.45/1.29  tff(f_127, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.45/1.29  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.45/1.29  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.45/1.29  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.45/1.29  tff(f_66, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.45/1.29  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.45/1.29  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.45/1.29  tff(f_94, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 2.45/1.29  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.45/1.29  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.45/1.29  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.45/1.29  tff(c_61, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.45/1.29  tff(c_65, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_61])).
% 2.45/1.29  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.45/1.29  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.45/1.29  tff(c_67, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.29  tff(c_71, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_67])).
% 2.45/1.29  tff(c_79, plain, (![B_57, A_58]: (k1_relat_1(B_57)=A_58 | ~v1_partfun1(B_57, A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.29  tff(c_82, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_79])).
% 2.45/1.29  tff(c_85, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_82])).
% 2.45/1.29  tff(c_86, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_85])).
% 2.45/1.29  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.45/1.29  tff(c_87, plain, (![C_59, A_60, B_61]: (v1_partfun1(C_59, A_60) | ~v1_funct_2(C_59, A_60, B_61) | ~v1_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | v1_xboole_0(B_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.45/1.29  tff(c_90, plain, (v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_87])).
% 2.45/1.29  tff(c_93, plain, (v1_partfun1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_90])).
% 2.45/1.29  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_86, c_93])).
% 2.45/1.29  tff(c_96, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_85])).
% 2.45/1.29  tff(c_34, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.45/1.29  tff(c_6, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.45/1.29  tff(c_109, plain, (![B_64]: (r2_hidden('#skF_1'(k1_relat_1(B_64), B_64), k1_relat_1(B_64)) | k6_partfun1(k1_relat_1(B_64))=B_64 | ~v1_funct_1(B_64) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 2.45/1.29  tff(c_115, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), k1_relat_1('#skF_4')) | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_96, c_109])).
% 2.45/1.29  tff(c_121, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_96, c_96, c_115])).
% 2.45/1.29  tff(c_132, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_121])).
% 2.45/1.29  tff(c_36, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.45/1.29  tff(c_133, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_36])).
% 2.45/1.29  tff(c_28, plain, (![D_28, A_20, B_21, C_22]: (k1_funct_1(D_28, '#skF_2'(A_20, B_21, C_22, D_28))!=k1_funct_1(C_22, '#skF_2'(A_20, B_21, C_22, D_28)) | r2_funct_2(A_20, B_21, C_22, D_28) | ~m1_subset_1(D_28, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(D_28, A_20, B_21) | ~v1_funct_1(D_28) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.45/1.29  tff(c_232, plain, (![A_94, B_95, C_96]: (r2_funct_2(A_94, B_95, C_96, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96))), inference(reflexivity, [status(thm), theory('equality')], [c_28])).
% 2.45/1.29  tff(c_234, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_232])).
% 2.45/1.29  tff(c_237, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_234])).
% 2.45/1.29  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_237])).
% 2.45/1.29  tff(c_241, plain, (k6_partfun1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_121])).
% 2.45/1.29  tff(c_4, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.45/1.29  tff(c_269, plain, (![B_98]: (k1_funct_1(B_98, '#skF_1'(k1_relat_1(B_98), B_98))!='#skF_1'(k1_relat_1(B_98), B_98) | k6_partfun1(k1_relat_1(B_98))=B_98 | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4])).
% 2.45/1.29  tff(c_272, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'(k1_relat_1('#skF_4'), '#skF_4') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_96, c_269])).
% 2.45/1.29  tff(c_274, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'('#skF_3', '#skF_4') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_44, c_96, c_96, c_272])).
% 2.45/1.29  tff(c_275, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_241, c_274])).
% 2.45/1.29  tff(c_240, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_121])).
% 2.45/1.29  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.29  tff(c_245, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_240, c_2])).
% 2.45/1.29  tff(c_38, plain, (![C_41]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', C_41)=C_41 | ~m1_subset_1(C_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.45/1.29  tff(c_249, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_245, c_38])).
% 2.45/1.29  tff(c_276, plain, (![A_99, B_100, C_101, D_102]: (k3_funct_2(A_99, B_100, C_101, D_102)=k1_funct_1(C_101, D_102) | ~m1_subset_1(D_102, A_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_101, A_99, B_100) | ~v1_funct_1(C_101) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.45/1.29  tff(c_280, plain, (![B_100, C_101]: (k3_funct_2('#skF_3', B_100, C_101, '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1(C_101, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_100))) | ~v1_funct_2(C_101, '#skF_3', B_100) | ~v1_funct_1(C_101) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_245, c_276])).
% 2.45/1.29  tff(c_302, plain, (![B_108, C_109]: (k3_funct_2('#skF_3', B_108, C_109, '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1(C_109, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_108))) | ~v1_funct_2(C_109, '#skF_3', B_108) | ~v1_funct_1(C_109))), inference(negUnitSimplification, [status(thm)], [c_46, c_280])).
% 2.45/1.29  tff(c_305, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_302])).
% 2.45/1.29  tff(c_308, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_249, c_305])).
% 2.45/1.29  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_308])).
% 2.45/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.29  
% 2.45/1.29  Inference rules
% 2.45/1.29  ----------------------
% 2.45/1.29  #Ref     : 1
% 2.45/1.29  #Sup     : 50
% 2.45/1.29  #Fact    : 0
% 2.45/1.29  #Define  : 0
% 2.45/1.29  #Split   : 4
% 2.45/1.29  #Chain   : 0
% 2.45/1.29  #Close   : 0
% 2.45/1.29  
% 2.45/1.29  Ordering : KBO
% 2.45/1.29  
% 2.45/1.29  Simplification rules
% 2.45/1.29  ----------------------
% 2.45/1.29  #Subsume      : 0
% 2.45/1.29  #Demod        : 93
% 2.45/1.29  #Tautology    : 24
% 2.45/1.29  #SimpNegUnit  : 12
% 2.45/1.29  #BackRed      : 1
% 2.45/1.29  
% 2.45/1.29  #Partial instantiations: 0
% 2.45/1.29  #Strategies tried      : 1
% 2.45/1.29  
% 2.45/1.29  Timing (in seconds)
% 2.45/1.29  ----------------------
% 2.45/1.29  Preprocessing        : 0.33
% 2.45/1.29  Parsing              : 0.17
% 2.45/1.29  CNF conversion       : 0.02
% 2.45/1.29  Main loop            : 0.23
% 2.45/1.29  Inferencing          : 0.09
% 2.45/1.29  Reduction            : 0.07
% 2.45/1.29  Demodulation         : 0.05
% 2.45/1.29  BG Simplification    : 0.02
% 2.45/1.29  Subsumption          : 0.03
% 2.45/1.29  Abstraction          : 0.01
% 2.45/1.29  MUC search           : 0.00
% 2.45/1.29  Cooper               : 0.00
% 2.45/1.29  Total                : 0.59
% 2.45/1.29  Index Insertion      : 0.00
% 2.45/1.29  Index Deletion       : 0.00
% 2.45/1.30  Index Matching       : 0.00
% 2.45/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
