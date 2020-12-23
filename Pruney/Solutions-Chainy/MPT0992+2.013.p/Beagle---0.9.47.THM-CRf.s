%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:33 EST 2020

% Result     : Theorem 9.00s
% Output     : CNFRefutation 9.39s
% Verified   : 
% Statistics : Number of formulae       :  192 (1512 expanded)
%              Number of leaves         :   42 ( 473 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 (4504 expanded)
%              Number of equality atoms :   75 (1451 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_64,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_91,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_91])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9692,plain,(
    ! [A_843,B_844,C_845] :
      ( k1_relset_1(A_843,B_844,C_845) = k1_relat_1(C_845)
      | ~ m1_subset_1(C_845,k1_zfmisc_1(k2_zfmisc_1(A_843,B_844))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9704,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_9692])).

tff(c_9997,plain,(
    ! [B_894,A_895,C_896] :
      ( k1_xboole_0 = B_894
      | k1_relset_1(A_895,B_894,C_896) = A_895
      | ~ v1_funct_2(C_896,A_895,B_894)
      | ~ m1_subset_1(C_896,k1_zfmisc_1(k2_zfmisc_1(A_895,B_894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_10003,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_9997])).

tff(c_10011,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_9704,c_10003])).

tff(c_10012,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_10011])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( k1_relat_1(k7_relat_1(B_12,A_11)) = A_11
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10032,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10012,c_22])).

tff(c_10044,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_10032])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_9934,plain,(
    ! [A_884,B_885,C_886,D_887] :
      ( k2_partfun1(A_884,B_885,C_886,D_887) = k7_relat_1(C_886,D_887)
      | ~ m1_subset_1(C_886,k1_zfmisc_1(k2_zfmisc_1(A_884,B_885)))
      | ~ v1_funct_1(C_886) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_9940,plain,(
    ! [D_887] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_887) = k7_relat_1('#skF_4',D_887)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_9934])).

tff(c_9950,plain,(
    ! [D_887] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_887) = k7_relat_1('#skF_4',D_887) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9940])).

tff(c_697,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k2_partfun1(A_163,B_164,C_165,D_166) = k7_relat_1(C_165,D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_701,plain,(
    ! [D_166] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_166) = k7_relat_1('#skF_4',D_166)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_697])).

tff(c_708,plain,(
    ! [D_166] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_166) = k7_relat_1('#skF_4',D_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_701])).

tff(c_989,plain,(
    ! [A_198,B_199,C_200,D_201] :
      ( m1_subset_1(k2_partfun1(A_198,B_199,C_200,D_201),k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1037,plain,(
    ! [D_166] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_166),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_989])).

tff(c_1132,plain,(
    ! [D_208] : m1_subset_1(k7_relat_1('#skF_4',D_208),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1037])).

tff(c_26,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1182,plain,(
    ! [D_208] : v1_relat_1(k7_relat_1('#skF_4',D_208)) ),
    inference(resolution,[status(thm)],[c_1132,c_26])).

tff(c_28,plain,(
    ! [C_21,B_20,A_19] :
      ( v5_relat_1(C_21,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1180,plain,(
    ! [D_208] : v5_relat_1(k7_relat_1('#skF_4',D_208),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1132,c_28])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_539,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( v1_funct_1(k2_partfun1(A_137,B_138,C_139,D_140))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_541,plain,(
    ! [D_140] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_140))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_539])).

tff(c_547,plain,(
    ! [D_140] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_140)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_541])).

tff(c_712,plain,(
    ! [D_140] : v1_funct_1(k7_relat_1('#skF_4',D_140)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_547])).

tff(c_471,plain,(
    ! [A_126,B_127,C_128] :
      ( k1_relset_1(A_126,B_127,C_128) = k1_relat_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_479,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_471])).

tff(c_735,plain,(
    ! [B_173,A_174,C_175] :
      ( k1_xboole_0 = B_173
      | k1_relset_1(A_174,B_173,C_175) = A_174
      | ~ v1_funct_2(C_175,A_174,B_173)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_741,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_735])).

tff(c_749,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_479,c_741])).

tff(c_750,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_749])).

tff(c_770,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_11)) = A_11
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_22])).

tff(c_815,plain,(
    ! [A_180] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_180)) = A_180
      | ~ r1_tarski(A_180,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_770])).

tff(c_54,plain,(
    ! [B_41,A_40] :
      ( m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41),A_40)))
      | ~ r1_tarski(k2_relat_1(B_41),A_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_826,plain,(
    ! [A_180,A_40] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_180),k1_zfmisc_1(k2_zfmisc_1(A_180,A_40)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_180)),A_40)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_180))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_180))
      | ~ r1_tarski(A_180,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_54])).

tff(c_850,plain,(
    ! [A_180,A_40] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_180),k1_zfmisc_1(k2_zfmisc_1(A_180,A_40)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_180)),A_40)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_180))
      | ~ r1_tarski(A_180,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_826])).

tff(c_9437,plain,(
    ! [A_833,A_834] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_833),k1_zfmisc_1(k2_zfmisc_1(A_833,A_834)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_833)),A_834)
      | ~ r1_tarski(A_833,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_850])).

tff(c_320,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( v1_funct_1(k2_partfun1(A_94,B_95,C_96,D_97))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_322,plain,(
    ! [D_97] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_97))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_320])).

tff(c_328,plain,(
    ! [D_97] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_322])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_117,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_117])).

tff(c_335,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_416,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_713,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_416])).

tff(c_9473,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_9437,c_713])).

tff(c_9552,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_9473])).

tff(c_9580,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_9552])).

tff(c_9584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_1180,c_9580])).

tff(c_9586,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_9703,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9586,c_9692])).

tff(c_9956,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9950,c_9950,c_9703])).

tff(c_9585,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_9963,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9950,c_9585])).

tff(c_9962,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9950,c_9586])).

tff(c_10184,plain,(
    ! [B_903,C_904,A_905] :
      ( k1_xboole_0 = B_903
      | v1_funct_2(C_904,A_905,B_903)
      | k1_relset_1(A_905,B_903,C_904) != A_905
      | ~ m1_subset_1(C_904,k1_zfmisc_1(k2_zfmisc_1(A_905,B_903))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_10187,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_9962,c_10184])).

tff(c_10200,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9963,c_83,c_10187])).

tff(c_10221,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9956,c_10200])).

tff(c_10228,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10044,c_10221])).

tff(c_10232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10228])).

tff(c_10233,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_10234,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_10244,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_10234])).

tff(c_10269,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10244,c_66])).

tff(c_10275,plain,(
    ! [C_915,A_916,B_917] :
      ( v1_relat_1(C_915)
      | ~ m1_subset_1(C_915,k1_zfmisc_1(k2_zfmisc_1(A_916,B_917))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10283,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10269,c_10275])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10239,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_2])).

tff(c_11655,plain,(
    ! [C_1098,A_1099,B_1100] :
      ( v1_xboole_0(C_1098)
      | ~ m1_subset_1(C_1098,k1_zfmisc_1(k2_zfmisc_1(A_1099,B_1100)))
      | ~ v1_xboole_0(A_1099) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_11661,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10269,c_11655])).

tff(c_11671,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10239,c_11661])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10259,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_4])).

tff(c_11677,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11671,c_10259])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10235,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_10])).

tff(c_10284,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10235,c_10275])).

tff(c_10730,plain,(
    ! [C_975,B_976,A_977] :
      ( v5_relat_1(C_975,B_976)
      | ~ m1_subset_1(C_975,k1_zfmisc_1(k2_zfmisc_1(A_977,B_976))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10739,plain,(
    ! [B_976] : v5_relat_1('#skF_1',B_976) ),
    inference(resolution,[status(thm)],[c_10235,c_10730])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10236,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_10233,c_18])).

tff(c_10741,plain,(
    ! [B_979,A_980] :
      ( r1_tarski(k2_relat_1(B_979),A_980)
      | ~ v5_relat_1(B_979,A_980)
      | ~ v1_relat_1(B_979) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10748,plain,(
    ! [A_980] :
      ( r1_tarski('#skF_1',A_980)
      | ~ v5_relat_1('#skF_1',A_980)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10236,c_10741])).

tff(c_10751,plain,(
    ! [A_980] : r1_tarski('#skF_1',A_980) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10284,c_10739,c_10748])).

tff(c_11692,plain,(
    ! [A_980] : r1_tarski('#skF_4',A_980) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_10751])).

tff(c_11703,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_11677,c_10236])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10237,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_10233,c_20])).

tff(c_11704,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_11677,c_10237])).

tff(c_11846,plain,(
    ! [B_1117,A_1118] :
      ( v1_funct_2(B_1117,k1_relat_1(B_1117),A_1118)
      | ~ r1_tarski(k2_relat_1(B_1117),A_1118)
      | ~ v1_funct_1(B_1117)
      | ~ v1_relat_1(B_1117) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_11849,plain,(
    ! [A_1118] :
      ( v1_funct_2('#skF_4','#skF_4',A_1118)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1118)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11704,c_11846])).

tff(c_11851,plain,(
    ! [A_1118] : v1_funct_2('#skF_4','#skF_4',A_1118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10283,c_70,c_11692,c_11703,c_11849])).

tff(c_10835,plain,(
    ! [C_991,A_992,B_993] :
      ( v1_xboole_0(C_991)
      | ~ m1_subset_1(C_991,k1_zfmisc_1(k2_zfmisc_1(A_992,B_993)))
      | ~ v1_xboole_0(A_992) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10838,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10269,c_10835])).

tff(c_10845,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10239,c_10838])).

tff(c_10851,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10845,c_10259])).

tff(c_10866,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10851,c_10235])).

tff(c_11246,plain,(
    ! [A_1052,B_1053,C_1054,D_1055] :
      ( k2_partfun1(A_1052,B_1053,C_1054,D_1055) = k7_relat_1(C_1054,D_1055)
      | ~ m1_subset_1(C_1054,k1_zfmisc_1(k2_zfmisc_1(A_1052,B_1053)))
      | ~ v1_funct_1(C_1054) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_11251,plain,(
    ! [A_1052,B_1053,D_1055] :
      ( k2_partfun1(A_1052,B_1053,'#skF_4',D_1055) = k7_relat_1('#skF_4',D_1055)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10866,c_11246])).

tff(c_11255,plain,(
    ! [A_1052,B_1053,D_1055] : k2_partfun1(A_1052,B_1053,'#skF_4',D_1055) = k7_relat_1('#skF_4',D_1055) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11251])).

tff(c_11412,plain,(
    ! [A_1072,B_1073,C_1074,D_1075] :
      ( m1_subset_1(k2_partfun1(A_1072,B_1073,C_1074,D_1075),k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1073)))
      | ~ m1_subset_1(C_1074,k1_zfmisc_1(k2_zfmisc_1(A_1072,B_1073)))
      | ~ v1_funct_1(C_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_11457,plain,(
    ! [D_1055,A_1052,B_1053] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_1055),k1_zfmisc_1(k2_zfmisc_1(A_1052,B_1053)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1052,B_1053)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11255,c_11412])).

tff(c_11473,plain,(
    ! [D_1055,A_1052,B_1053] : m1_subset_1(k7_relat_1('#skF_4',D_1055),k1_zfmisc_1(k2_zfmisc_1(A_1052,B_1053))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10866,c_11457])).

tff(c_6,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10238,plain,(
    ! [A_2] : r1_xboole_0(A_2,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10233,c_6])).

tff(c_10270,plain,(
    ! [B_913,A_914] :
      ( ~ r1_xboole_0(B_913,A_914)
      | ~ r1_tarski(B_913,A_914)
      | v1_xboole_0(B_913) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10285,plain,(
    ! [A_918] :
      ( ~ r1_tarski(A_918,'#skF_1')
      | v1_xboole_0(A_918) ) ),
    inference(resolution,[status(thm)],[c_10238,c_10270])).

tff(c_10289,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_10285])).

tff(c_10716,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10289,c_10259])).

tff(c_10445,plain,(
    ! [C_944,A_945,B_946] :
      ( v1_xboole_0(C_944)
      | ~ m1_subset_1(C_944,k1_zfmisc_1(k2_zfmisc_1(A_945,B_946)))
      | ~ v1_xboole_0(A_945) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10448,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10269,c_10445])).

tff(c_10455,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10239,c_10448])).

tff(c_10477,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10455,c_10259])).

tff(c_10494,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10477,c_10235])).

tff(c_10701,plain,(
    ! [A_971,B_972,C_973,D_974] :
      ( v1_funct_1(k2_partfun1(A_971,B_972,C_973,D_974))
      | ~ m1_subset_1(C_973,k1_zfmisc_1(k2_zfmisc_1(A_971,B_972)))
      | ~ v1_funct_1(C_973) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10704,plain,(
    ! [A_971,B_972,D_974] :
      ( v1_funct_1(k2_partfun1(A_971,B_972,'#skF_4',D_974))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10494,c_10701])).

tff(c_10707,plain,(
    ! [A_971,B_972,D_974] : v1_funct_1(k2_partfun1(A_971,B_972,'#skF_4',D_974)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10704])).

tff(c_10295,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10289,c_10259])).

tff(c_10290,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10244,c_10244,c_10244,c_10244,c_10244,c_60])).

tff(c_10291,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10290])).

tff(c_10308,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10295,c_10291])).

tff(c_10488,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10477,c_10477,c_10477,c_10308])).

tff(c_10710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10707,c_10488])).

tff(c_10711,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_10290])).

tff(c_10752,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10716,c_10716,c_10716,c_10716,c_10711])).

tff(c_10753,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_10752])).

tff(c_10852,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10851,c_10851,c_10851,c_10851,c_10851,c_10753])).

tff(c_11257,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11255,c_10852])).

tff(c_11482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11473,c_11257])).

tff(c_11484,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_10752])).

tff(c_11658,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_11484,c_11655])).

tff(c_11668,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10239,c_11658])).

tff(c_11841,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_11677,c_11677,c_11668])).

tff(c_11701,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_10259])).

tff(c_11845,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11841,c_11701])).

tff(c_11483,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_10752])).

tff(c_11690,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11677,c_11677,c_11677,c_11677,c_11677,c_11483])).

tff(c_11880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11851,c_11845,c_11690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.00/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.00/3.29  
% 9.00/3.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.00/3.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.00/3.29  
% 9.00/3.29  %Foreground sorts:
% 9.00/3.29  
% 9.00/3.29  
% 9.00/3.29  %Background operators:
% 9.00/3.29  
% 9.00/3.29  
% 9.00/3.29  %Foreground operators:
% 9.00/3.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.00/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.00/3.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.00/3.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.00/3.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.00/3.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.00/3.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.00/3.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.00/3.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.00/3.29  tff('#skF_2', type, '#skF_2': $i).
% 9.00/3.29  tff('#skF_3', type, '#skF_3': $i).
% 9.00/3.29  tff('#skF_1', type, '#skF_1': $i).
% 9.00/3.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.00/3.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.00/3.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.00/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.00/3.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.00/3.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.00/3.29  tff('#skF_4', type, '#skF_4': $i).
% 9.00/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.00/3.29  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.00/3.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.00/3.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.00/3.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.00/3.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.00/3.29  
% 9.39/3.32  tff(f_157, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 9.39/3.32  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.39/3.32  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.39/3.32  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.39/3.32  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.39/3.32  tff(f_125, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.39/3.32  tff(f_119, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.39/3.32  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.39/3.32  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.39/3.32  tff(f_137, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.39/3.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.39/3.32  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 9.39/3.32  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.39/3.32  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 9.39/3.32  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.39/3.32  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.39/3.32  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 9.39/3.32  tff(c_64, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.39/3.32  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.39/3.32  tff(c_91, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.39/3.32  tff(c_99, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_91])).
% 9.39/3.32  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.39/3.32  tff(c_83, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 9.39/3.32  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.39/3.32  tff(c_9692, plain, (![A_843, B_844, C_845]: (k1_relset_1(A_843, B_844, C_845)=k1_relat_1(C_845) | ~m1_subset_1(C_845, k1_zfmisc_1(k2_zfmisc_1(A_843, B_844))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.39/3.32  tff(c_9704, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_9692])).
% 9.39/3.32  tff(c_9997, plain, (![B_894, A_895, C_896]: (k1_xboole_0=B_894 | k1_relset_1(A_895, B_894, C_896)=A_895 | ~v1_funct_2(C_896, A_895, B_894) | ~m1_subset_1(C_896, k1_zfmisc_1(k2_zfmisc_1(A_895, B_894))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.32  tff(c_10003, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_9997])).
% 9.39/3.32  tff(c_10011, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_9704, c_10003])).
% 9.39/3.32  tff(c_10012, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_83, c_10011])).
% 9.39/3.32  tff(c_22, plain, (![B_12, A_11]: (k1_relat_1(k7_relat_1(B_12, A_11))=A_11 | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.39/3.32  tff(c_10032, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10012, c_22])).
% 9.39/3.32  tff(c_10044, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_10032])).
% 9.39/3.32  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.39/3.32  tff(c_9934, plain, (![A_884, B_885, C_886, D_887]: (k2_partfun1(A_884, B_885, C_886, D_887)=k7_relat_1(C_886, D_887) | ~m1_subset_1(C_886, k1_zfmisc_1(k2_zfmisc_1(A_884, B_885))) | ~v1_funct_1(C_886))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.39/3.32  tff(c_9940, plain, (![D_887]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_887)=k7_relat_1('#skF_4', D_887) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_9934])).
% 9.39/3.32  tff(c_9950, plain, (![D_887]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_887)=k7_relat_1('#skF_4', D_887))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9940])).
% 9.39/3.32  tff(c_697, plain, (![A_163, B_164, C_165, D_166]: (k2_partfun1(A_163, B_164, C_165, D_166)=k7_relat_1(C_165, D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.39/3.32  tff(c_701, plain, (![D_166]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_166)=k7_relat_1('#skF_4', D_166) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_697])).
% 9.39/3.32  tff(c_708, plain, (![D_166]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_166)=k7_relat_1('#skF_4', D_166))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_701])).
% 9.39/3.32  tff(c_989, plain, (![A_198, B_199, C_200, D_201]: (m1_subset_1(k2_partfun1(A_198, B_199, C_200, D_201), k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.39/3.32  tff(c_1037, plain, (![D_166]: (m1_subset_1(k7_relat_1('#skF_4', D_166), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_708, c_989])).
% 9.39/3.32  tff(c_1132, plain, (![D_208]: (m1_subset_1(k7_relat_1('#skF_4', D_208), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1037])).
% 9.39/3.32  tff(c_26, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.39/3.32  tff(c_1182, plain, (![D_208]: (v1_relat_1(k7_relat_1('#skF_4', D_208)))), inference(resolution, [status(thm)], [c_1132, c_26])).
% 9.39/3.32  tff(c_28, plain, (![C_21, B_20, A_19]: (v5_relat_1(C_21, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.39/3.32  tff(c_1180, plain, (![D_208]: (v5_relat_1(k7_relat_1('#skF_4', D_208), '#skF_2'))), inference(resolution, [status(thm)], [c_1132, c_28])).
% 9.39/3.32  tff(c_16, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.39/3.32  tff(c_539, plain, (![A_137, B_138, C_139, D_140]: (v1_funct_1(k2_partfun1(A_137, B_138, C_139, D_140)) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.39/3.32  tff(c_541, plain, (![D_140]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_140)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_539])).
% 9.39/3.32  tff(c_547, plain, (![D_140]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_140)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_541])).
% 9.39/3.32  tff(c_712, plain, (![D_140]: (v1_funct_1(k7_relat_1('#skF_4', D_140)))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_547])).
% 9.39/3.32  tff(c_471, plain, (![A_126, B_127, C_128]: (k1_relset_1(A_126, B_127, C_128)=k1_relat_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.39/3.32  tff(c_479, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_471])).
% 9.39/3.32  tff(c_735, plain, (![B_173, A_174, C_175]: (k1_xboole_0=B_173 | k1_relset_1(A_174, B_173, C_175)=A_174 | ~v1_funct_2(C_175, A_174, B_173) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.32  tff(c_741, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_735])).
% 9.39/3.32  tff(c_749, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_479, c_741])).
% 9.39/3.32  tff(c_750, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_83, c_749])).
% 9.39/3.32  tff(c_770, plain, (![A_11]: (k1_relat_1(k7_relat_1('#skF_4', A_11))=A_11 | ~r1_tarski(A_11, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_750, c_22])).
% 9.39/3.32  tff(c_815, plain, (![A_180]: (k1_relat_1(k7_relat_1('#skF_4', A_180))=A_180 | ~r1_tarski(A_180, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_770])).
% 9.39/3.32  tff(c_54, plain, (![B_41, A_40]: (m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_41), A_40))) | ~r1_tarski(k2_relat_1(B_41), A_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.39/3.32  tff(c_826, plain, (![A_180, A_40]: (m1_subset_1(k7_relat_1('#skF_4', A_180), k1_zfmisc_1(k2_zfmisc_1(A_180, A_40))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_180)), A_40) | ~v1_funct_1(k7_relat_1('#skF_4', A_180)) | ~v1_relat_1(k7_relat_1('#skF_4', A_180)) | ~r1_tarski(A_180, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_815, c_54])).
% 9.39/3.32  tff(c_850, plain, (![A_180, A_40]: (m1_subset_1(k7_relat_1('#skF_4', A_180), k1_zfmisc_1(k2_zfmisc_1(A_180, A_40))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_180)), A_40) | ~v1_relat_1(k7_relat_1('#skF_4', A_180)) | ~r1_tarski(A_180, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_826])).
% 9.39/3.32  tff(c_9437, plain, (![A_833, A_834]: (m1_subset_1(k7_relat_1('#skF_4', A_833), k1_zfmisc_1(k2_zfmisc_1(A_833, A_834))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_833)), A_834) | ~r1_tarski(A_833, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1182, c_850])).
% 9.39/3.32  tff(c_320, plain, (![A_94, B_95, C_96, D_97]: (v1_funct_1(k2_partfun1(A_94, B_95, C_96, D_97)) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.39/3.32  tff(c_322, plain, (![D_97]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_97)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_320])).
% 9.39/3.32  tff(c_328, plain, (![D_97]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_97)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_322])).
% 9.39/3.32  tff(c_60, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.39/3.32  tff(c_117, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 9.39/3.32  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_328, c_117])).
% 9.39/3.32  tff(c_335, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_60])).
% 9.39/3.32  tff(c_416, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_335])).
% 9.39/3.32  tff(c_713, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_416])).
% 9.39/3.32  tff(c_9473, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_9437, c_713])).
% 9.39/3.32  tff(c_9552, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_9473])).
% 9.39/3.32  tff(c_9580, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_9552])).
% 9.39/3.32  tff(c_9584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1182, c_1180, c_9580])).
% 9.39/3.32  tff(c_9586, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_335])).
% 9.39/3.32  tff(c_9703, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_9586, c_9692])).
% 9.39/3.32  tff(c_9956, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9950, c_9950, c_9703])).
% 9.39/3.32  tff(c_9585, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_335])).
% 9.39/3.32  tff(c_9963, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9950, c_9585])).
% 9.39/3.32  tff(c_9962, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9950, c_9586])).
% 9.39/3.32  tff(c_10184, plain, (![B_903, C_904, A_905]: (k1_xboole_0=B_903 | v1_funct_2(C_904, A_905, B_903) | k1_relset_1(A_905, B_903, C_904)!=A_905 | ~m1_subset_1(C_904, k1_zfmisc_1(k2_zfmisc_1(A_905, B_903))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.39/3.32  tff(c_10187, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_9962, c_10184])).
% 9.39/3.32  tff(c_10200, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_9963, c_83, c_10187])).
% 9.39/3.32  tff(c_10221, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9956, c_10200])).
% 9.39/3.32  tff(c_10228, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10044, c_10221])).
% 9.39/3.32  tff(c_10232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_10228])).
% 9.39/3.32  tff(c_10233, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 9.39/3.32  tff(c_10234, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 9.39/3.32  tff(c_10244, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_10234])).
% 9.39/3.32  tff(c_10269, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10244, c_66])).
% 9.39/3.32  tff(c_10275, plain, (![C_915, A_916, B_917]: (v1_relat_1(C_915) | ~m1_subset_1(C_915, k1_zfmisc_1(k2_zfmisc_1(A_916, B_917))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.39/3.32  tff(c_10283, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10269, c_10275])).
% 9.39/3.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.39/3.32  tff(c_10239, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_2])).
% 9.39/3.32  tff(c_11655, plain, (![C_1098, A_1099, B_1100]: (v1_xboole_0(C_1098) | ~m1_subset_1(C_1098, k1_zfmisc_1(k2_zfmisc_1(A_1099, B_1100))) | ~v1_xboole_0(A_1099))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.39/3.32  tff(c_11661, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10269, c_11655])).
% 9.39/3.32  tff(c_11671, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10239, c_11661])).
% 9.39/3.32  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.39/3.32  tff(c_10259, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_4])).
% 9.39/3.32  tff(c_11677, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_11671, c_10259])).
% 9.39/3.32  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.39/3.32  tff(c_10235, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_10])).
% 9.39/3.32  tff(c_10284, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10235, c_10275])).
% 9.39/3.32  tff(c_10730, plain, (![C_975, B_976, A_977]: (v5_relat_1(C_975, B_976) | ~m1_subset_1(C_975, k1_zfmisc_1(k2_zfmisc_1(A_977, B_976))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.39/3.32  tff(c_10739, plain, (![B_976]: (v5_relat_1('#skF_1', B_976))), inference(resolution, [status(thm)], [c_10235, c_10730])).
% 9.39/3.32  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.39/3.32  tff(c_10236, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_10233, c_18])).
% 9.39/3.32  tff(c_10741, plain, (![B_979, A_980]: (r1_tarski(k2_relat_1(B_979), A_980) | ~v5_relat_1(B_979, A_980) | ~v1_relat_1(B_979))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.39/3.32  tff(c_10748, plain, (![A_980]: (r1_tarski('#skF_1', A_980) | ~v5_relat_1('#skF_1', A_980) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10236, c_10741])).
% 9.39/3.32  tff(c_10751, plain, (![A_980]: (r1_tarski('#skF_1', A_980))), inference(demodulation, [status(thm), theory('equality')], [c_10284, c_10739, c_10748])).
% 9.39/3.32  tff(c_11692, plain, (![A_980]: (r1_tarski('#skF_4', A_980))), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_10751])).
% 9.39/3.32  tff(c_11703, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_11677, c_10236])).
% 9.39/3.32  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.39/3.32  tff(c_10237, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_10233, c_20])).
% 9.39/3.32  tff(c_11704, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_11677, c_10237])).
% 9.39/3.32  tff(c_11846, plain, (![B_1117, A_1118]: (v1_funct_2(B_1117, k1_relat_1(B_1117), A_1118) | ~r1_tarski(k2_relat_1(B_1117), A_1118) | ~v1_funct_1(B_1117) | ~v1_relat_1(B_1117))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.39/3.32  tff(c_11849, plain, (![A_1118]: (v1_funct_2('#skF_4', '#skF_4', A_1118) | ~r1_tarski(k2_relat_1('#skF_4'), A_1118) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11704, c_11846])).
% 9.39/3.32  tff(c_11851, plain, (![A_1118]: (v1_funct_2('#skF_4', '#skF_4', A_1118))), inference(demodulation, [status(thm), theory('equality')], [c_10283, c_70, c_11692, c_11703, c_11849])).
% 9.39/3.32  tff(c_10835, plain, (![C_991, A_992, B_993]: (v1_xboole_0(C_991) | ~m1_subset_1(C_991, k1_zfmisc_1(k2_zfmisc_1(A_992, B_993))) | ~v1_xboole_0(A_992))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.39/3.32  tff(c_10838, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10269, c_10835])).
% 9.39/3.32  tff(c_10845, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10239, c_10838])).
% 9.39/3.32  tff(c_10851, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_10845, c_10259])).
% 9.39/3.32  tff(c_10866, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10851, c_10235])).
% 9.39/3.32  tff(c_11246, plain, (![A_1052, B_1053, C_1054, D_1055]: (k2_partfun1(A_1052, B_1053, C_1054, D_1055)=k7_relat_1(C_1054, D_1055) | ~m1_subset_1(C_1054, k1_zfmisc_1(k2_zfmisc_1(A_1052, B_1053))) | ~v1_funct_1(C_1054))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.39/3.32  tff(c_11251, plain, (![A_1052, B_1053, D_1055]: (k2_partfun1(A_1052, B_1053, '#skF_4', D_1055)=k7_relat_1('#skF_4', D_1055) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10866, c_11246])).
% 9.39/3.32  tff(c_11255, plain, (![A_1052, B_1053, D_1055]: (k2_partfun1(A_1052, B_1053, '#skF_4', D_1055)=k7_relat_1('#skF_4', D_1055))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_11251])).
% 9.39/3.32  tff(c_11412, plain, (![A_1072, B_1073, C_1074, D_1075]: (m1_subset_1(k2_partfun1(A_1072, B_1073, C_1074, D_1075), k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1073))) | ~m1_subset_1(C_1074, k1_zfmisc_1(k2_zfmisc_1(A_1072, B_1073))) | ~v1_funct_1(C_1074))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.39/3.32  tff(c_11457, plain, (![D_1055, A_1052, B_1053]: (m1_subset_1(k7_relat_1('#skF_4', D_1055), k1_zfmisc_1(k2_zfmisc_1(A_1052, B_1053))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1052, B_1053))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11255, c_11412])).
% 9.39/3.32  tff(c_11473, plain, (![D_1055, A_1052, B_1053]: (m1_subset_1(k7_relat_1('#skF_4', D_1055), k1_zfmisc_1(k2_zfmisc_1(A_1052, B_1053))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10866, c_11457])).
% 9.39/3.32  tff(c_6, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.39/3.32  tff(c_10238, plain, (![A_2]: (r1_xboole_0(A_2, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10233, c_6])).
% 9.39/3.32  tff(c_10270, plain, (![B_913, A_914]: (~r1_xboole_0(B_913, A_914) | ~r1_tarski(B_913, A_914) | v1_xboole_0(B_913))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.39/3.32  tff(c_10285, plain, (![A_918]: (~r1_tarski(A_918, '#skF_1') | v1_xboole_0(A_918))), inference(resolution, [status(thm)], [c_10238, c_10270])).
% 9.39/3.32  tff(c_10289, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_10285])).
% 9.39/3.32  tff(c_10716, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_10289, c_10259])).
% 9.39/3.32  tff(c_10445, plain, (![C_944, A_945, B_946]: (v1_xboole_0(C_944) | ~m1_subset_1(C_944, k1_zfmisc_1(k2_zfmisc_1(A_945, B_946))) | ~v1_xboole_0(A_945))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.39/3.32  tff(c_10448, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10269, c_10445])).
% 9.39/3.32  tff(c_10455, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10239, c_10448])).
% 9.39/3.32  tff(c_10477, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_10455, c_10259])).
% 9.39/3.32  tff(c_10494, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10477, c_10235])).
% 9.39/3.32  tff(c_10701, plain, (![A_971, B_972, C_973, D_974]: (v1_funct_1(k2_partfun1(A_971, B_972, C_973, D_974)) | ~m1_subset_1(C_973, k1_zfmisc_1(k2_zfmisc_1(A_971, B_972))) | ~v1_funct_1(C_973))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.39/3.32  tff(c_10704, plain, (![A_971, B_972, D_974]: (v1_funct_1(k2_partfun1(A_971, B_972, '#skF_4', D_974)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10494, c_10701])).
% 9.39/3.32  tff(c_10707, plain, (![A_971, B_972, D_974]: (v1_funct_1(k2_partfun1(A_971, B_972, '#skF_4', D_974)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10704])).
% 9.39/3.32  tff(c_10295, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_10289, c_10259])).
% 9.39/3.32  tff(c_10290, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10244, c_10244, c_10244, c_10244, c_10244, c_60])).
% 9.39/3.32  tff(c_10291, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_10290])).
% 9.39/3.32  tff(c_10308, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10295, c_10291])).
% 9.39/3.32  tff(c_10488, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10477, c_10477, c_10477, c_10308])).
% 9.39/3.32  tff(c_10710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10707, c_10488])).
% 9.39/3.32  tff(c_10711, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_10290])).
% 9.39/3.32  tff(c_10752, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10716, c_10716, c_10716, c_10716, c_10711])).
% 9.39/3.32  tff(c_10753, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_10752])).
% 9.39/3.32  tff(c_10852, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10851, c_10851, c_10851, c_10851, c_10851, c_10753])).
% 9.39/3.32  tff(c_11257, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11255, c_10852])).
% 9.39/3.32  tff(c_11482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11473, c_11257])).
% 9.39/3.32  tff(c_11484, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_10752])).
% 9.39/3.32  tff(c_11658, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_11484, c_11655])).
% 9.39/3.32  tff(c_11668, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10239, c_11658])).
% 9.39/3.32  tff(c_11841, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_11677, c_11677, c_11668])).
% 9.39/3.32  tff(c_11701, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_10259])).
% 9.39/3.32  tff(c_11845, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_11841, c_11701])).
% 9.39/3.32  tff(c_11483, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_10752])).
% 9.39/3.32  tff(c_11690, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11677, c_11677, c_11677, c_11677, c_11677, c_11483])).
% 9.39/3.32  tff(c_11880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11851, c_11845, c_11690])).
% 9.39/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.39/3.32  
% 9.39/3.32  Inference rules
% 9.39/3.32  ----------------------
% 9.39/3.32  #Ref     : 0
% 9.39/3.32  #Sup     : 2540
% 9.39/3.32  #Fact    : 0
% 9.39/3.32  #Define  : 0
% 9.39/3.32  #Split   : 21
% 9.39/3.32  #Chain   : 0
% 9.39/3.32  #Close   : 0
% 9.39/3.32  
% 9.39/3.32  Ordering : KBO
% 9.39/3.32  
% 9.39/3.32  Simplification rules
% 9.39/3.32  ----------------------
% 9.39/3.32  #Subsume      : 402
% 9.39/3.32  #Demod        : 4915
% 9.39/3.32  #Tautology    : 1230
% 9.39/3.32  #SimpNegUnit  : 85
% 9.39/3.32  #BackRed      : 160
% 9.39/3.32  
% 9.39/3.32  #Partial instantiations: 0
% 9.39/3.32  #Strategies tried      : 1
% 9.39/3.32  
% 9.39/3.32  Timing (in seconds)
% 9.39/3.32  ----------------------
% 9.39/3.32  Preprocessing        : 0.35
% 9.39/3.32  Parsing              : 0.18
% 9.39/3.32  CNF conversion       : 0.02
% 9.39/3.32  Main loop            : 2.17
% 9.39/3.32  Inferencing          : 0.64
% 9.39/3.32  Reduction            : 0.93
% 9.39/3.32  Demodulation         : 0.73
% 9.39/3.32  BG Simplification    : 0.06
% 9.39/3.32  Subsumption          : 0.40
% 9.39/3.32  Abstraction          : 0.08
% 9.39/3.32  MUC search           : 0.00
% 9.39/3.32  Cooper               : 0.00
% 9.39/3.32  Total                : 2.58
% 9.39/3.32  Index Insertion      : 0.00
% 9.39/3.32  Index Deletion       : 0.00
% 9.39/3.32  Index Matching       : 0.00
% 9.39/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
