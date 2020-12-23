%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:11 EST 2020

% Result     : Theorem 8.76s
% Output     : CNFRefutation 9.04s
% Verified   : 
% Statistics : Number of formulae       :  236 (2171 expanded)
%              Number of leaves         :   37 ( 724 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 (6276 expanded)
%              Number of equality atoms :  126 (1979 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_26,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_162,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_174,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_162])).

tff(c_184,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_174])).

tff(c_15367,plain,(
    ! [C_1163,A_1164,B_1165] :
      ( v4_relat_1(C_1163,A_1164)
      | ~ m1_subset_1(C_1163,k1_zfmisc_1(k2_zfmisc_1(A_1164,B_1165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_15386,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_15367])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15458,plain,(
    ! [A_1174,B_1175,C_1176] :
      ( k2_relset_1(A_1174,B_1175,C_1176) = k2_relat_1(C_1176)
      | ~ m1_subset_1(C_1176,k1_zfmisc_1(k2_zfmisc_1(A_1174,B_1175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_15478,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_15458])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_15496,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15478,c_60])).

tff(c_15631,plain,(
    ! [C_1199,A_1200,B_1201] :
      ( m1_subset_1(C_1199,k1_zfmisc_1(k2_zfmisc_1(A_1200,B_1201)))
      | ~ r1_tarski(k2_relat_1(C_1199),B_1201)
      | ~ r1_tarski(k1_relat_1(C_1199),A_1200)
      | ~ v1_relat_1(C_1199) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_113,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_10752,plain,(
    ! [A_861,B_862,C_863] :
      ( k1_relset_1(A_861,B_862,C_863) = k1_relat_1(C_863)
      | ~ m1_subset_1(C_863,k1_zfmisc_1(k2_zfmisc_1(A_861,B_862))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10772,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_10752])).

tff(c_11133,plain,(
    ! [B_907,A_908,C_909] :
      ( k1_xboole_0 = B_907
      | k1_relset_1(A_908,B_907,C_909) = A_908
      | ~ v1_funct_2(C_909,A_908,B_907)
      | ~ m1_subset_1(C_909,k1_zfmisc_1(k2_zfmisc_1(A_908,B_907))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11146,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_11133])).

tff(c_11159,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_10772,c_11146])).

tff(c_11160,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_11159])).

tff(c_7502,plain,(
    ! [A_631,B_632,C_633] :
      ( k1_relset_1(A_631,B_632,C_633) = k1_relat_1(C_633)
      | ~ m1_subset_1(C_633,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7522,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_7502])).

tff(c_7671,plain,(
    ! [B_653,A_654,C_655] :
      ( k1_xboole_0 = B_653
      | k1_relset_1(A_654,B_653,C_655) = A_654
      | ~ v1_funct_2(C_655,A_654,B_653)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_654,B_653))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7684,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_7671])).

tff(c_7697,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_7522,c_7684])).

tff(c_7698,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_7697])).

tff(c_7339,plain,(
    ! [A_615,B_616,C_617] :
      ( k2_relset_1(A_615,B_616,C_617) = k2_relat_1(C_617)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_615,B_616))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7359,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_7339])).

tff(c_7378,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7359,c_60])).

tff(c_7543,plain,(
    ! [C_635,A_636,B_637] :
      ( m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_636,B_637)))
      | ~ r1_tarski(k2_relat_1(C_635),B_637)
      | ~ r1_tarski(k1_relat_1(C_635),A_636)
      | ~ v1_relat_1(C_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8719,plain,(
    ! [C_745,A_746,B_747] :
      ( r1_tarski(C_745,k2_zfmisc_1(A_746,B_747))
      | ~ r1_tarski(k2_relat_1(C_745),B_747)
      | ~ r1_tarski(k1_relat_1(C_745),A_746)
      | ~ v1_relat_1(C_745) ) ),
    inference(resolution,[status(thm)],[c_7543,c_16])).

tff(c_8721,plain,(
    ! [A_746] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_746,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_746)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7378,c_8719])).

tff(c_8858,plain,(
    ! [A_751] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_751,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_751) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_7698,c_8721])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7521,plain,(
    ! [A_631,B_632,A_6] :
      ( k1_relset_1(A_631,B_632,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_631,B_632)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7502])).

tff(c_8863,plain,(
    ! [A_751] :
      ( k1_relset_1(A_751,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_751) ) ),
    inference(resolution,[status(thm)],[c_8858,c_7521])).

tff(c_9015,plain,(
    ! [A_754] :
      ( k1_relset_1(A_754,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_754) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7698,c_8863])).

tff(c_9020,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_9015])).

tff(c_8731,plain,(
    ! [A_746] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_746,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_746) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_7698,c_8721])).

tff(c_7787,plain,(
    ! [B_664,C_665,A_666] :
      ( k1_xboole_0 = B_664
      | v1_funct_2(C_665,A_666,B_664)
      | k1_relset_1(A_666,B_664,C_665) != A_666
      | ~ m1_subset_1(C_665,k1_zfmisc_1(k2_zfmisc_1(A_666,B_664))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9941,plain,(
    ! [B_804,A_805,A_806] :
      ( k1_xboole_0 = B_804
      | v1_funct_2(A_805,A_806,B_804)
      | k1_relset_1(A_806,B_804,A_805) != A_806
      | ~ r1_tarski(A_805,k2_zfmisc_1(A_806,B_804)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7787])).

tff(c_9979,plain,(
    ! [A_746] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_746,'#skF_3')
      | k1_relset_1(A_746,'#skF_3','#skF_4') != A_746
      | ~ r1_tarski('#skF_1',A_746) ) ),
    inference(resolution,[status(thm)],[c_8731,c_9941])).

tff(c_10063,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9979])).

tff(c_42,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_168,plain,(
    ! [A_28] :
      ( v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k2_zfmisc_1(A_28,A_28)) ) ),
    inference(resolution,[status(thm)],[c_42,c_162])).

tff(c_180,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_168])).

tff(c_28,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8430,plain,(
    ! [C_726,B_727] :
      ( m1_subset_1(C_726,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_726),B_727)
      | ~ r1_tarski(k1_relat_1(C_726),k1_xboole_0)
      | ~ v1_relat_1(C_726) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7543])).

tff(c_8479,plain,(
    ! [C_734] :
      ( m1_subset_1(C_734,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_734),k1_xboole_0)
      | ~ v1_relat_1(C_734) ) ),
    inference(resolution,[status(thm)],[c_6,c_8430])).

tff(c_8492,plain,(
    ! [A_15] :
      ( m1_subset_1(k6_relat_1(A_15),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(A_15,k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8479])).

tff(c_8500,plain,(
    ! [A_735] :
      ( m1_subset_1(k6_relat_1(A_735),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(A_735,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_8492])).

tff(c_8601,plain,(
    ! [A_742] :
      ( r1_tarski(k6_relat_1(A_742),k1_xboole_0)
      | ~ r1_tarski(A_742,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8500,c_16])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7300,plain,(
    ! [C_608,A_609,B_610] :
      ( v4_relat_1(C_608,A_609)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_609,B_610))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7330,plain,(
    ! [C_613,A_614] :
      ( v4_relat_1(C_613,A_614)
      | ~ m1_subset_1(C_613,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7300])).

tff(c_7338,plain,(
    ! [A_6,A_614] :
      ( v4_relat_1(A_6,A_614)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_7330])).

tff(c_7199,plain,(
    ! [B_593,A_594] :
      ( r1_tarski(k1_relat_1(B_593),A_594)
      | ~ v4_relat_1(B_593,A_594)
      | ~ v1_relat_1(B_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8062,plain,(
    ! [B_690,A_691] :
      ( k1_relat_1(B_690) = A_691
      | ~ r1_tarski(A_691,k1_relat_1(B_690))
      | ~ v4_relat_1(B_690,A_691)
      | ~ v1_relat_1(B_690) ) ),
    inference(resolution,[status(thm)],[c_7199,c_2])).

tff(c_8075,plain,(
    ! [A_15,A_691] :
      ( k1_relat_1(k6_relat_1(A_15)) = A_691
      | ~ r1_tarski(A_691,A_15)
      | ~ v4_relat_1(k6_relat_1(A_15),A_691)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8062])).

tff(c_8127,plain,(
    ! [A_696,A_695] :
      ( A_696 = A_695
      | ~ r1_tarski(A_695,A_696)
      | ~ v4_relat_1(k6_relat_1(A_696),A_695) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_28,c_8075])).

tff(c_8173,plain,(
    ! [A_700,A_699] :
      ( A_700 = A_699
      | ~ r1_tarski(A_700,A_699)
      | ~ r1_tarski(k6_relat_1(A_699),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7338,c_8127])).

tff(c_8186,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski(k6_relat_1('#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7378,c_8173])).

tff(c_8200,plain,(
    ~ r1_tarski(k6_relat_1('#skF_3'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8186])).

tff(c_8647,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8601,c_8200])).

tff(c_10094,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10063,c_8647])).

tff(c_10154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10094])).

tff(c_10585,plain,(
    ! [A_840] :
      ( v1_funct_2('#skF_4',A_840,'#skF_3')
      | k1_relset_1(A_840,'#skF_3','#skF_4') != A_840
      | ~ r1_tarski('#skF_1',A_840) ) ),
    inference(splitRight,[status(thm)],[c_9979])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_56])).

tff(c_239,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_10596,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10585,c_239])).

tff(c_10606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9020,c_10596])).

tff(c_10607,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8186])).

tff(c_186,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_186])).

tff(c_7171,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_7376,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7359,c_7171])).

tff(c_10609,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10607,c_7376])).

tff(c_10615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10609])).

tff(c_10616,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_10849,plain,(
    ! [A_875,B_876,C_877] :
      ( k2_relset_1(A_875,B_876,C_877) = k2_relat_1(C_877)
      | ~ m1_subset_1(C_877,k1_zfmisc_1(k2_zfmisc_1(A_875,B_876))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10859,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_10849])).

tff(c_10870,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10616,c_10859])).

tff(c_11003,plain,(
    ! [C_890,A_891,B_892] :
      ( m1_subset_1(C_890,k1_zfmisc_1(k2_zfmisc_1(A_891,B_892)))
      | ~ r1_tarski(k2_relat_1(C_890),B_892)
      | ~ r1_tarski(k1_relat_1(C_890),A_891)
      | ~ v1_relat_1(C_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_13579,plain,(
    ! [A_1071,B_1072,C_1073] :
      ( k1_relset_1(A_1071,B_1072,C_1073) = k1_relat_1(C_1073)
      | ~ r1_tarski(k2_relat_1(C_1073),B_1072)
      | ~ r1_tarski(k1_relat_1(C_1073),A_1071)
      | ~ v1_relat_1(C_1073) ) ),
    inference(resolution,[status(thm)],[c_11003,c_36])).

tff(c_13581,plain,(
    ! [A_1071,B_1072] :
      ( k1_relset_1(A_1071,B_1072,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_1072)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1071)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10870,c_13579])).

tff(c_13636,plain,(
    ! [A_1078,B_1079] :
      ( k1_relset_1(A_1078,B_1079,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_1079)
      | ~ r1_tarski('#skF_1',A_1078) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_11160,c_11160,c_13581])).

tff(c_13641,plain,(
    ! [A_1080] :
      ( k1_relset_1(A_1080,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_1080) ) ),
    inference(resolution,[status(thm)],[c_6,c_13636])).

tff(c_13646,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_13641])).

tff(c_40,plain,(
    ! [C_27,A_25,B_26] :
      ( m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ r1_tarski(k2_relat_1(C_27),B_26)
      | ~ r1_tarski(k1_relat_1(C_27),A_25)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11253,plain,(
    ! [B_917,C_918,A_919] :
      ( k1_xboole_0 = B_917
      | v1_funct_2(C_918,A_919,B_917)
      | k1_relset_1(A_919,B_917,C_918) != A_919
      | ~ m1_subset_1(C_918,k1_zfmisc_1(k2_zfmisc_1(A_919,B_917))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_13934,plain,(
    ! [B_1100,C_1101,A_1102] :
      ( k1_xboole_0 = B_1100
      | v1_funct_2(C_1101,A_1102,B_1100)
      | k1_relset_1(A_1102,B_1100,C_1101) != A_1102
      | ~ r1_tarski(k2_relat_1(C_1101),B_1100)
      | ~ r1_tarski(k1_relat_1(C_1101),A_1102)
      | ~ v1_relat_1(C_1101) ) ),
    inference(resolution,[status(thm)],[c_40,c_11253])).

tff(c_13936,plain,(
    ! [B_1100,A_1102] :
      ( k1_xboole_0 = B_1100
      | v1_funct_2('#skF_4',A_1102,B_1100)
      | k1_relset_1(A_1102,B_1100,'#skF_4') != A_1102
      | ~ r1_tarski('#skF_3',B_1100)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1102)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10870,c_13934])).

tff(c_14125,plain,(
    ! [B_1109,A_1110] :
      ( k1_xboole_0 = B_1109
      | v1_funct_2('#skF_4',A_1110,B_1109)
      | k1_relset_1(A_1110,B_1109,'#skF_4') != A_1110
      | ~ r1_tarski('#skF_3',B_1109)
      | ~ r1_tarski('#skF_1',A_1110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_11160,c_13936])).

tff(c_14136,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_14125,c_239])).

tff(c_14144,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_13646,c_14136])).

tff(c_12161,plain,(
    ! [C_998,A_999] :
      ( m1_subset_1(C_998,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_998),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_998),A_999)
      | ~ v1_relat_1(C_998) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_11003])).

tff(c_12163,plain,(
    ! [A_999] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_999)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10870,c_12161])).

tff(c_12169,plain,(
    ! [A_999] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_999) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_11160,c_12163])).

tff(c_12219,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12169])).

tff(c_14184,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14144,c_12219])).

tff(c_14247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14184])).

tff(c_14249,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12169])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_14296,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14249,c_209])).

tff(c_10700,plain,(
    ! [C_854,A_855,B_856] :
      ( v4_relat_1(C_854,A_855)
      | ~ m1_subset_1(C_854,k1_zfmisc_1(k2_zfmisc_1(A_855,B_856))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10743,plain,(
    ! [C_859,A_860] :
      ( v4_relat_1(C_859,A_860)
      | ~ m1_subset_1(C_859,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_10700])).

tff(c_10751,plain,(
    ! [A_6,A_860] :
      ( v4_relat_1(A_6,A_860)
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_10743])).

tff(c_11166,plain,(
    ! [A_11] :
      ( r1_tarski('#skF_1',A_11)
      | ~ v4_relat_1('#skF_4',A_11)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11160,c_24])).

tff(c_11194,plain,(
    ! [A_911] :
      ( r1_tarski('#skF_1',A_911)
      | ~ v4_relat_1('#skF_4',A_911) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_11166])).

tff(c_11206,plain,(
    ! [A_860] :
      ( r1_tarski('#skF_1',A_860)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10751,c_11194])).

tff(c_11237,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11206])).

tff(c_14330,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_11237])).

tff(c_14644,plain,(
    ! [A_1128] : k2_zfmisc_1(A_1128,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_14296,c_12])).

tff(c_14361,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14296,c_8])).

tff(c_14369,plain,(
    ! [C_1111,A_1112,B_1113] :
      ( r1_tarski(C_1111,k2_zfmisc_1(A_1112,B_1113))
      | ~ r1_tarski(k2_relat_1(C_1111),B_1113)
      | ~ r1_tarski(k1_relat_1(C_1111),A_1112)
      | ~ v1_relat_1(C_1111) ) ),
    inference(resolution,[status(thm)],[c_11003,c_16])).

tff(c_14371,plain,(
    ! [A_1112,B_1113] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1112,B_1113))
      | ~ r1_tarski('#skF_3',B_1113)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1112)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10870,c_14369])).

tff(c_14378,plain,(
    ! [A_1112,B_1113] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1112,B_1113))
      | ~ r1_tarski('#skF_3',B_1113)
      | ~ r1_tarski('#skF_1',A_1112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_11160,c_14371])).

tff(c_14518,plain,(
    ! [A_1112,B_1113] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1112,B_1113))
      | ~ r1_tarski('#skF_1',A_1112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14361,c_14378])).

tff(c_14655,plain,(
    ! [A_1128] :
      ( r1_tarski('#skF_4','#skF_3')
      | ~ r1_tarski('#skF_1',A_1128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14644,c_14518])).

tff(c_14733,plain,(
    ! [A_1129] : ~ r1_tarski('#skF_1',A_1129) ),
    inference(negUnitSimplification,[status(thm)],[c_14330,c_14655])).

tff(c_14738,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_14733])).

tff(c_14739,plain,(
    ! [A_860] : r1_tarski('#skF_1',A_860) ),
    inference(splitRight,[status(thm)],[c_11206])).

tff(c_14744,plain,(
    ! [A_1130] : r1_tarski('#skF_1',A_1130) ),
    inference(splitRight,[status(thm)],[c_11206])).

tff(c_14778,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14744,c_209])).

tff(c_14740,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11206])).

tff(c_14829,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14778,c_14740])).

tff(c_14834,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_14829,c_2])).

tff(c_14840,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14739,c_14834])).

tff(c_124,plain,(
    ! [A_42] : m1_subset_1(k6_relat_1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_128,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_124])).

tff(c_134,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_128,c_134])).

tff(c_190,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_147,c_186])).

tff(c_202,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_225,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_28])).

tff(c_212,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_128])).

tff(c_11114,plain,(
    ! [B_904,C_905] :
      ( k1_relset_1(k1_xboole_0,B_904,C_905) = k1_relat_1(C_905)
      | ~ m1_subset_1(C_905,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_10752])).

tff(c_11116,plain,(
    ! [B_904] : k1_relset_1(k1_xboole_0,B_904,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_212,c_11114])).

tff(c_11121,plain,(
    ! [B_904] : k1_relset_1(k1_xboole_0,B_904,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_11116])).

tff(c_48,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11098,plain,(
    ! [C_901,B_902] :
      ( v1_funct_2(C_901,k1_xboole_0,B_902)
      | k1_relset_1(k1_xboole_0,B_902,C_901) != k1_xboole_0
      | ~ m1_subset_1(C_901,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_11104,plain,(
    ! [B_902] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_902)
      | k1_relset_1(k1_xboole_0,B_902,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_212,c_11098])).

tff(c_11124,plain,(
    ! [B_902] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_902) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11121,c_11104])).

tff(c_14790,plain,(
    ! [B_902] : v1_funct_2('#skF_1','#skF_1',B_902) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14778,c_14778,c_11124])).

tff(c_15188,plain,(
    ! [B_902] : v1_funct_2('#skF_4','#skF_4',B_902) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14840,c_14840,c_14790])).

tff(c_30,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_228,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_30])).

tff(c_14815,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14778,c_14778,c_228])).

tff(c_14937,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14840,c_10870,c_14840,c_14815])).

tff(c_14875,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14840,c_239])).

tff(c_15192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15188,c_14937,c_14875])).

tff(c_15193,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_15646,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15631,c_15193])).

tff(c_15665,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_15496,c_15646])).

tff(c_15672,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_15665])).

tff(c_15676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_15386,c_15672])).

tff(c_15677,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15682,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_8])).

tff(c_15681,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_15677,c_14])).

tff(c_15678,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_15687,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_15678])).

tff(c_15731,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15681,c_15687,c_62])).

tff(c_15733,plain,(
    ! [A_1206,B_1207] :
      ( r1_tarski(A_1206,B_1207)
      | ~ m1_subset_1(A_1206,k1_zfmisc_1(B_1207)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_15737,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_15731,c_15733])).

tff(c_15811,plain,(
    ! [B_1217,A_1218] :
      ( B_1217 = A_1218
      | ~ r1_tarski(B_1217,A_1218)
      | ~ r1_tarski(A_1218,B_1217) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15817,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_15737,c_15811])).

tff(c_15830,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15682,c_15817])).

tff(c_15679,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_15677,c_12])).

tff(c_15743,plain,(
    ! [A_1210] : m1_subset_1(k6_relat_1(A_1210),k1_zfmisc_1(k2_zfmisc_1(A_1210,A_1210))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_15750,plain,(
    m1_subset_1(k6_relat_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15679,c_15743])).

tff(c_15771,plain,(
    r1_tarski(k6_relat_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_15750,c_16])).

tff(c_15815,plain,
    ( k6_relat_1('#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k6_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_15771,c_15811])).

tff(c_15827,plain,(
    k6_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15682,c_15815])).

tff(c_15869,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15830,c_15830,c_15827])).

tff(c_15881,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_15869,c_28])).

tff(c_15847,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15830,c_15682])).

tff(c_16297,plain,(
    ! [A_1269,B_1270,C_1271] :
      ( k1_relset_1(A_1269,B_1270,C_1271) = k1_relat_1(C_1271)
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(k2_zfmisc_1(A_1269,B_1270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16687,plain,(
    ! [A_1317,B_1318,A_1319] :
      ( k1_relset_1(A_1317,B_1318,A_1319) = k1_relat_1(A_1319)
      | ~ r1_tarski(A_1319,k2_zfmisc_1(A_1317,B_1318)) ) ),
    inference(resolution,[status(thm)],[c_18,c_16297])).

tff(c_16701,plain,(
    ! [A_1317,B_1318] : k1_relset_1(A_1317,B_1318,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_15847,c_16687])).

tff(c_16711,plain,(
    ! [A_1317,B_1318] : k1_relset_1(A_1317,B_1318,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15881,c_16701])).

tff(c_15843,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15830,c_15731])).

tff(c_15850,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15830,c_15677])).

tff(c_70,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_16802,plain,(
    ! [C_1330,B_1331] :
      ( v1_funct_2(C_1330,'#skF_4',B_1331)
      | k1_relset_1('#skF_4',B_1331,C_1330) != '#skF_4'
      | ~ m1_subset_1(C_1330,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15850,c_15850,c_15850,c_15850,c_70])).

tff(c_16804,plain,(
    ! [B_1331] :
      ( v1_funct_2('#skF_4','#skF_4',B_1331)
      | k1_relset_1('#skF_4',B_1331,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_15843,c_16802])).

tff(c_16810,plain,(
    ! [B_1331] : v1_funct_2('#skF_4','#skF_4',B_1331) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16711,c_16804])).

tff(c_15774,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15731,c_15681,c_68])).

tff(c_15837,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15830,c_15774])).

tff(c_16815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16810,c_15837])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:45:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.76/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.04/3.20  
% 9.04/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.04/3.20  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.04/3.20  
% 9.04/3.20  %Foreground sorts:
% 9.04/3.20  
% 9.04/3.20  
% 9.04/3.20  %Background operators:
% 9.04/3.20  
% 9.04/3.20  
% 9.04/3.20  %Foreground operators:
% 9.04/3.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.04/3.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.04/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.04/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.04/3.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.04/3.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.04/3.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.04/3.20  tff('#skF_2', type, '#skF_2': $i).
% 9.04/3.20  tff('#skF_3', type, '#skF_3': $i).
% 9.04/3.20  tff('#skF_1', type, '#skF_1': $i).
% 9.04/3.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.04/3.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.04/3.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.04/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.04/3.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.04/3.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.04/3.20  tff('#skF_4', type, '#skF_4': $i).
% 9.04/3.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.04/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.04/3.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.04/3.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.04/3.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.04/3.20  
% 9.04/3.23  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.04/3.23  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 9.04/3.23  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.04/3.23  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.04/3.23  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.04/3.23  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.04/3.23  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.04/3.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.04/3.23  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.04/3.23  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.04/3.23  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.04/3.23  tff(f_86, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.04/3.23  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.04/3.23  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.04/3.23  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.04/3.23  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.04/3.23  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.04/3.23  tff(c_162, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.04/3.23  tff(c_174, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_162])).
% 9.04/3.23  tff(c_184, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_174])).
% 9.04/3.23  tff(c_15367, plain, (![C_1163, A_1164, B_1165]: (v4_relat_1(C_1163, A_1164) | ~m1_subset_1(C_1163, k1_zfmisc_1(k2_zfmisc_1(A_1164, B_1165))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.04/3.23  tff(c_15386, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_15367])).
% 9.04/3.23  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.04/3.23  tff(c_15458, plain, (![A_1174, B_1175, C_1176]: (k2_relset_1(A_1174, B_1175, C_1176)=k2_relat_1(C_1176) | ~m1_subset_1(C_1176, k1_zfmisc_1(k2_zfmisc_1(A_1174, B_1175))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.04/3.23  tff(c_15478, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_15458])).
% 9.04/3.23  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.04/3.23  tff(c_15496, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15478, c_60])).
% 9.04/3.23  tff(c_15631, plain, (![C_1199, A_1200, B_1201]: (m1_subset_1(C_1199, k1_zfmisc_1(k2_zfmisc_1(A_1200, B_1201))) | ~r1_tarski(k2_relat_1(C_1199), B_1201) | ~r1_tarski(k1_relat_1(C_1199), A_1200) | ~v1_relat_1(C_1199))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.04/3.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.04/3.23  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.04/3.23  tff(c_113, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 9.04/3.23  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.04/3.23  tff(c_10752, plain, (![A_861, B_862, C_863]: (k1_relset_1(A_861, B_862, C_863)=k1_relat_1(C_863) | ~m1_subset_1(C_863, k1_zfmisc_1(k2_zfmisc_1(A_861, B_862))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.04/3.23  tff(c_10772, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_10752])).
% 9.04/3.23  tff(c_11133, plain, (![B_907, A_908, C_909]: (k1_xboole_0=B_907 | k1_relset_1(A_908, B_907, C_909)=A_908 | ~v1_funct_2(C_909, A_908, B_907) | ~m1_subset_1(C_909, k1_zfmisc_1(k2_zfmisc_1(A_908, B_907))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.23  tff(c_11146, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_11133])).
% 9.04/3.23  tff(c_11159, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_10772, c_11146])).
% 9.04/3.23  tff(c_11160, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_113, c_11159])).
% 9.04/3.23  tff(c_7502, plain, (![A_631, B_632, C_633]: (k1_relset_1(A_631, B_632, C_633)=k1_relat_1(C_633) | ~m1_subset_1(C_633, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.04/3.23  tff(c_7522, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_7502])).
% 9.04/3.23  tff(c_7671, plain, (![B_653, A_654, C_655]: (k1_xboole_0=B_653 | k1_relset_1(A_654, B_653, C_655)=A_654 | ~v1_funct_2(C_655, A_654, B_653) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_654, B_653))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.23  tff(c_7684, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_7671])).
% 9.04/3.23  tff(c_7697, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_7522, c_7684])).
% 9.04/3.23  tff(c_7698, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_113, c_7697])).
% 9.04/3.23  tff(c_7339, plain, (![A_615, B_616, C_617]: (k2_relset_1(A_615, B_616, C_617)=k2_relat_1(C_617) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_615, B_616))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.04/3.23  tff(c_7359, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_7339])).
% 9.04/3.23  tff(c_7378, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7359, c_60])).
% 9.04/3.23  tff(c_7543, plain, (![C_635, A_636, B_637]: (m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_636, B_637))) | ~r1_tarski(k2_relat_1(C_635), B_637) | ~r1_tarski(k1_relat_1(C_635), A_636) | ~v1_relat_1(C_635))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.04/3.23  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.04/3.23  tff(c_8719, plain, (![C_745, A_746, B_747]: (r1_tarski(C_745, k2_zfmisc_1(A_746, B_747)) | ~r1_tarski(k2_relat_1(C_745), B_747) | ~r1_tarski(k1_relat_1(C_745), A_746) | ~v1_relat_1(C_745))), inference(resolution, [status(thm)], [c_7543, c_16])).
% 9.04/3.23  tff(c_8721, plain, (![A_746]: (r1_tarski('#skF_4', k2_zfmisc_1(A_746, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_746) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7378, c_8719])).
% 9.04/3.23  tff(c_8858, plain, (![A_751]: (r1_tarski('#skF_4', k2_zfmisc_1(A_751, '#skF_3')) | ~r1_tarski('#skF_1', A_751))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_7698, c_8721])).
% 9.04/3.23  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.04/3.23  tff(c_7521, plain, (![A_631, B_632, A_6]: (k1_relset_1(A_631, B_632, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_631, B_632)))), inference(resolution, [status(thm)], [c_18, c_7502])).
% 9.04/3.23  tff(c_8863, plain, (![A_751]: (k1_relset_1(A_751, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_751))), inference(resolution, [status(thm)], [c_8858, c_7521])).
% 9.04/3.23  tff(c_9015, plain, (![A_754]: (k1_relset_1(A_754, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_754))), inference(demodulation, [status(thm), theory('equality')], [c_7698, c_8863])).
% 9.04/3.23  tff(c_9020, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_9015])).
% 9.04/3.23  tff(c_8731, plain, (![A_746]: (r1_tarski('#skF_4', k2_zfmisc_1(A_746, '#skF_3')) | ~r1_tarski('#skF_1', A_746))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_7698, c_8721])).
% 9.04/3.23  tff(c_7787, plain, (![B_664, C_665, A_666]: (k1_xboole_0=B_664 | v1_funct_2(C_665, A_666, B_664) | k1_relset_1(A_666, B_664, C_665)!=A_666 | ~m1_subset_1(C_665, k1_zfmisc_1(k2_zfmisc_1(A_666, B_664))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.23  tff(c_9941, plain, (![B_804, A_805, A_806]: (k1_xboole_0=B_804 | v1_funct_2(A_805, A_806, B_804) | k1_relset_1(A_806, B_804, A_805)!=A_806 | ~r1_tarski(A_805, k2_zfmisc_1(A_806, B_804)))), inference(resolution, [status(thm)], [c_18, c_7787])).
% 9.04/3.23  tff(c_9979, plain, (![A_746]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_746, '#skF_3') | k1_relset_1(A_746, '#skF_3', '#skF_4')!=A_746 | ~r1_tarski('#skF_1', A_746))), inference(resolution, [status(thm)], [c_8731, c_9941])).
% 9.04/3.23  tff(c_10063, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_9979])).
% 9.04/3.23  tff(c_42, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.04/3.23  tff(c_168, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k2_zfmisc_1(A_28, A_28)))), inference(resolution, [status(thm)], [c_42, c_162])).
% 9.04/3.23  tff(c_180, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_168])).
% 9.04/3.23  tff(c_28, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.04/3.23  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.04/3.23  tff(c_8430, plain, (![C_726, B_727]: (m1_subset_1(C_726, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_726), B_727) | ~r1_tarski(k1_relat_1(C_726), k1_xboole_0) | ~v1_relat_1(C_726))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7543])).
% 9.04/3.23  tff(c_8479, plain, (![C_734]: (m1_subset_1(C_734, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_734), k1_xboole_0) | ~v1_relat_1(C_734))), inference(resolution, [status(thm)], [c_6, c_8430])).
% 9.04/3.23  tff(c_8492, plain, (![A_15]: (m1_subset_1(k6_relat_1(A_15), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(A_15, k1_xboole_0) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8479])).
% 9.04/3.23  tff(c_8500, plain, (![A_735]: (m1_subset_1(k6_relat_1(A_735), k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(A_735, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_8492])).
% 9.04/3.23  tff(c_8601, plain, (![A_742]: (r1_tarski(k6_relat_1(A_742), k1_xboole_0) | ~r1_tarski(A_742, k1_xboole_0))), inference(resolution, [status(thm)], [c_8500, c_16])).
% 9.04/3.23  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.04/3.23  tff(c_7300, plain, (![C_608, A_609, B_610]: (v4_relat_1(C_608, A_609) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_609, B_610))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.04/3.23  tff(c_7330, plain, (![C_613, A_614]: (v4_relat_1(C_613, A_614) | ~m1_subset_1(C_613, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7300])).
% 9.04/3.23  tff(c_7338, plain, (![A_6, A_614]: (v4_relat_1(A_6, A_614) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_7330])).
% 9.04/3.23  tff(c_7199, plain, (![B_593, A_594]: (r1_tarski(k1_relat_1(B_593), A_594) | ~v4_relat_1(B_593, A_594) | ~v1_relat_1(B_593))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.04/3.23  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.04/3.23  tff(c_8062, plain, (![B_690, A_691]: (k1_relat_1(B_690)=A_691 | ~r1_tarski(A_691, k1_relat_1(B_690)) | ~v4_relat_1(B_690, A_691) | ~v1_relat_1(B_690))), inference(resolution, [status(thm)], [c_7199, c_2])).
% 9.04/3.23  tff(c_8075, plain, (![A_15, A_691]: (k1_relat_1(k6_relat_1(A_15))=A_691 | ~r1_tarski(A_691, A_15) | ~v4_relat_1(k6_relat_1(A_15), A_691) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8062])).
% 9.04/3.23  tff(c_8127, plain, (![A_696, A_695]: (A_696=A_695 | ~r1_tarski(A_695, A_696) | ~v4_relat_1(k6_relat_1(A_696), A_695))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_28, c_8075])).
% 9.04/3.23  tff(c_8173, plain, (![A_700, A_699]: (A_700=A_699 | ~r1_tarski(A_700, A_699) | ~r1_tarski(k6_relat_1(A_699), k1_xboole_0))), inference(resolution, [status(thm)], [c_7338, c_8127])).
% 9.04/3.23  tff(c_8186, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski(k6_relat_1('#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_7378, c_8173])).
% 9.04/3.23  tff(c_8200, plain, (~r1_tarski(k6_relat_1('#skF_3'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8186])).
% 9.04/3.23  tff(c_8647, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_8601, c_8200])).
% 9.04/3.23  tff(c_10094, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10063, c_8647])).
% 9.04/3.23  tff(c_10154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10094])).
% 9.04/3.23  tff(c_10585, plain, (![A_840]: (v1_funct_2('#skF_4', A_840, '#skF_3') | k1_relset_1(A_840, '#skF_3', '#skF_4')!=A_840 | ~r1_tarski('#skF_1', A_840))), inference(splitRight, [status(thm)], [c_9979])).
% 9.04/3.23  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.04/3.23  tff(c_56, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.04/3.23  tff(c_68, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_56])).
% 9.04/3.23  tff(c_239, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 9.04/3.23  tff(c_10596, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10585, c_239])).
% 9.04/3.23  tff(c_10606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9020, c_10596])).
% 9.04/3.23  tff(c_10607, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_8186])).
% 9.04/3.23  tff(c_186, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.04/3.23  tff(c_204, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_186])).
% 9.04/3.23  tff(c_7171, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_204])).
% 9.04/3.23  tff(c_7376, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7359, c_7171])).
% 9.04/3.23  tff(c_10609, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10607, c_7376])).
% 9.04/3.23  tff(c_10615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10609])).
% 9.04/3.23  tff(c_10616, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_204])).
% 9.04/3.23  tff(c_10849, plain, (![A_875, B_876, C_877]: (k2_relset_1(A_875, B_876, C_877)=k2_relat_1(C_877) | ~m1_subset_1(C_877, k1_zfmisc_1(k2_zfmisc_1(A_875, B_876))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.04/3.23  tff(c_10859, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_10849])).
% 9.04/3.23  tff(c_10870, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10616, c_10859])).
% 9.04/3.23  tff(c_11003, plain, (![C_890, A_891, B_892]: (m1_subset_1(C_890, k1_zfmisc_1(k2_zfmisc_1(A_891, B_892))) | ~r1_tarski(k2_relat_1(C_890), B_892) | ~r1_tarski(k1_relat_1(C_890), A_891) | ~v1_relat_1(C_890))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.04/3.23  tff(c_36, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.04/3.23  tff(c_13579, plain, (![A_1071, B_1072, C_1073]: (k1_relset_1(A_1071, B_1072, C_1073)=k1_relat_1(C_1073) | ~r1_tarski(k2_relat_1(C_1073), B_1072) | ~r1_tarski(k1_relat_1(C_1073), A_1071) | ~v1_relat_1(C_1073))), inference(resolution, [status(thm)], [c_11003, c_36])).
% 9.04/3.23  tff(c_13581, plain, (![A_1071, B_1072]: (k1_relset_1(A_1071, B_1072, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_1072) | ~r1_tarski(k1_relat_1('#skF_4'), A_1071) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10870, c_13579])).
% 9.04/3.23  tff(c_13636, plain, (![A_1078, B_1079]: (k1_relset_1(A_1078, B_1079, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_1079) | ~r1_tarski('#skF_1', A_1078))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_11160, c_11160, c_13581])).
% 9.04/3.23  tff(c_13641, plain, (![A_1080]: (k1_relset_1(A_1080, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_1080))), inference(resolution, [status(thm)], [c_6, c_13636])).
% 9.04/3.23  tff(c_13646, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_13641])).
% 9.04/3.23  tff(c_40, plain, (![C_27, A_25, B_26]: (m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~r1_tarski(k2_relat_1(C_27), B_26) | ~r1_tarski(k1_relat_1(C_27), A_25) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.04/3.23  tff(c_11253, plain, (![B_917, C_918, A_919]: (k1_xboole_0=B_917 | v1_funct_2(C_918, A_919, B_917) | k1_relset_1(A_919, B_917, C_918)!=A_919 | ~m1_subset_1(C_918, k1_zfmisc_1(k2_zfmisc_1(A_919, B_917))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.23  tff(c_13934, plain, (![B_1100, C_1101, A_1102]: (k1_xboole_0=B_1100 | v1_funct_2(C_1101, A_1102, B_1100) | k1_relset_1(A_1102, B_1100, C_1101)!=A_1102 | ~r1_tarski(k2_relat_1(C_1101), B_1100) | ~r1_tarski(k1_relat_1(C_1101), A_1102) | ~v1_relat_1(C_1101))), inference(resolution, [status(thm)], [c_40, c_11253])).
% 9.04/3.23  tff(c_13936, plain, (![B_1100, A_1102]: (k1_xboole_0=B_1100 | v1_funct_2('#skF_4', A_1102, B_1100) | k1_relset_1(A_1102, B_1100, '#skF_4')!=A_1102 | ~r1_tarski('#skF_3', B_1100) | ~r1_tarski(k1_relat_1('#skF_4'), A_1102) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10870, c_13934])).
% 9.04/3.23  tff(c_14125, plain, (![B_1109, A_1110]: (k1_xboole_0=B_1109 | v1_funct_2('#skF_4', A_1110, B_1109) | k1_relset_1(A_1110, B_1109, '#skF_4')!=A_1110 | ~r1_tarski('#skF_3', B_1109) | ~r1_tarski('#skF_1', A_1110))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_11160, c_13936])).
% 9.04/3.23  tff(c_14136, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_14125, c_239])).
% 9.04/3.23  tff(c_14144, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_13646, c_14136])).
% 9.04/3.23  tff(c_12161, plain, (![C_998, A_999]: (m1_subset_1(C_998, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_998), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_998), A_999) | ~v1_relat_1(C_998))), inference(superposition, [status(thm), theory('equality')], [c_12, c_11003])).
% 9.04/3.23  tff(c_12163, plain, (![A_999]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_999) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10870, c_12161])).
% 9.04/3.23  tff(c_12169, plain, (![A_999]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_999))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_11160, c_12163])).
% 9.04/3.23  tff(c_12219, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_12169])).
% 9.04/3.23  tff(c_14184, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14144, c_12219])).
% 9.04/3.23  tff(c_14247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14184])).
% 9.04/3.23  tff(c_14249, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_12169])).
% 9.04/3.23  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.04/3.23  tff(c_209, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_186])).
% 9.04/3.23  tff(c_14296, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14249, c_209])).
% 9.04/3.23  tff(c_10700, plain, (![C_854, A_855, B_856]: (v4_relat_1(C_854, A_855) | ~m1_subset_1(C_854, k1_zfmisc_1(k2_zfmisc_1(A_855, B_856))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.04/3.23  tff(c_10743, plain, (![C_859, A_860]: (v4_relat_1(C_859, A_860) | ~m1_subset_1(C_859, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_10700])).
% 9.04/3.23  tff(c_10751, plain, (![A_6, A_860]: (v4_relat_1(A_6, A_860) | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_10743])).
% 9.04/3.23  tff(c_11166, plain, (![A_11]: (r1_tarski('#skF_1', A_11) | ~v4_relat_1('#skF_4', A_11) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11160, c_24])).
% 9.04/3.23  tff(c_11194, plain, (![A_911]: (r1_tarski('#skF_1', A_911) | ~v4_relat_1('#skF_4', A_911))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_11166])).
% 9.04/3.23  tff(c_11206, plain, (![A_860]: (r1_tarski('#skF_1', A_860) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_10751, c_11194])).
% 9.04/3.23  tff(c_11237, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11206])).
% 9.04/3.23  tff(c_14330, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_11237])).
% 9.04/3.23  tff(c_14644, plain, (![A_1128]: (k2_zfmisc_1(A_1128, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_14296, c_12])).
% 9.04/3.23  tff(c_14361, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_14296, c_8])).
% 9.04/3.23  tff(c_14369, plain, (![C_1111, A_1112, B_1113]: (r1_tarski(C_1111, k2_zfmisc_1(A_1112, B_1113)) | ~r1_tarski(k2_relat_1(C_1111), B_1113) | ~r1_tarski(k1_relat_1(C_1111), A_1112) | ~v1_relat_1(C_1111))), inference(resolution, [status(thm)], [c_11003, c_16])).
% 9.04/3.23  tff(c_14371, plain, (![A_1112, B_1113]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1112, B_1113)) | ~r1_tarski('#skF_3', B_1113) | ~r1_tarski(k1_relat_1('#skF_4'), A_1112) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10870, c_14369])).
% 9.04/3.23  tff(c_14378, plain, (![A_1112, B_1113]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1112, B_1113)) | ~r1_tarski('#skF_3', B_1113) | ~r1_tarski('#skF_1', A_1112))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_11160, c_14371])).
% 9.04/3.23  tff(c_14518, plain, (![A_1112, B_1113]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1112, B_1113)) | ~r1_tarski('#skF_1', A_1112))), inference(demodulation, [status(thm), theory('equality')], [c_14361, c_14378])).
% 9.04/3.23  tff(c_14655, plain, (![A_1128]: (r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_1', A_1128))), inference(superposition, [status(thm), theory('equality')], [c_14644, c_14518])).
% 9.04/3.23  tff(c_14733, plain, (![A_1129]: (~r1_tarski('#skF_1', A_1129))), inference(negUnitSimplification, [status(thm)], [c_14330, c_14655])).
% 9.04/3.23  tff(c_14738, plain, $false, inference(resolution, [status(thm)], [c_6, c_14733])).
% 9.04/3.23  tff(c_14739, plain, (![A_860]: (r1_tarski('#skF_1', A_860))), inference(splitRight, [status(thm)], [c_11206])).
% 9.04/3.23  tff(c_14744, plain, (![A_1130]: (r1_tarski('#skF_1', A_1130))), inference(splitRight, [status(thm)], [c_11206])).
% 9.04/3.23  tff(c_14778, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14744, c_209])).
% 9.04/3.23  tff(c_14740, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_11206])).
% 9.04/3.23  tff(c_14829, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14778, c_14740])).
% 9.04/3.23  tff(c_14834, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_14829, c_2])).
% 9.04/3.23  tff(c_14840, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14739, c_14834])).
% 9.04/3.23  tff(c_124, plain, (![A_42]: (m1_subset_1(k6_relat_1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.04/3.23  tff(c_128, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_124])).
% 9.04/3.23  tff(c_134, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.04/3.23  tff(c_147, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_128, c_134])).
% 9.04/3.23  tff(c_190, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_147, c_186])).
% 9.04/3.23  tff(c_202, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_190])).
% 9.04/3.23  tff(c_225, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_202, c_28])).
% 9.04/3.23  tff(c_212, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_128])).
% 9.04/3.23  tff(c_11114, plain, (![B_904, C_905]: (k1_relset_1(k1_xboole_0, B_904, C_905)=k1_relat_1(C_905) | ~m1_subset_1(C_905, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_10752])).
% 9.04/3.23  tff(c_11116, plain, (![B_904]: (k1_relset_1(k1_xboole_0, B_904, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_212, c_11114])).
% 9.04/3.23  tff(c_11121, plain, (![B_904]: (k1_relset_1(k1_xboole_0, B_904, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_225, c_11116])).
% 9.04/3.23  tff(c_48, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.04/3.23  tff(c_11098, plain, (![C_901, B_902]: (v1_funct_2(C_901, k1_xboole_0, B_902) | k1_relset_1(k1_xboole_0, B_902, C_901)!=k1_xboole_0 | ~m1_subset_1(C_901, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 9.04/3.23  tff(c_11104, plain, (![B_902]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_902) | k1_relset_1(k1_xboole_0, B_902, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_212, c_11098])).
% 9.04/3.23  tff(c_11124, plain, (![B_902]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_902))), inference(demodulation, [status(thm), theory('equality')], [c_11121, c_11104])).
% 9.04/3.23  tff(c_14790, plain, (![B_902]: (v1_funct_2('#skF_1', '#skF_1', B_902))), inference(demodulation, [status(thm), theory('equality')], [c_14778, c_14778, c_11124])).
% 9.04/3.23  tff(c_15188, plain, (![B_902]: (v1_funct_2('#skF_4', '#skF_4', B_902))), inference(demodulation, [status(thm), theory('equality')], [c_14840, c_14840, c_14790])).
% 9.04/3.23  tff(c_30, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.04/3.23  tff(c_228, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_202, c_30])).
% 9.04/3.23  tff(c_14815, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14778, c_14778, c_228])).
% 9.04/3.23  tff(c_14937, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14840, c_10870, c_14840, c_14815])).
% 9.04/3.23  tff(c_14875, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14840, c_239])).
% 9.04/3.23  tff(c_15192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15188, c_14937, c_14875])).
% 9.04/3.23  tff(c_15193, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 9.04/3.23  tff(c_15646, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_15631, c_15193])).
% 9.04/3.23  tff(c_15665, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_15496, c_15646])).
% 9.04/3.23  tff(c_15672, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_15665])).
% 9.04/3.23  tff(c_15676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_15386, c_15672])).
% 9.04/3.23  tff(c_15677, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 9.04/3.23  tff(c_15682, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_8])).
% 9.04/3.23  tff(c_15681, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_15677, c_14])).
% 9.04/3.23  tff(c_15678, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 9.04/3.23  tff(c_15687, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_15678])).
% 9.04/3.23  tff(c_15731, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_15681, c_15687, c_62])).
% 9.04/3.23  tff(c_15733, plain, (![A_1206, B_1207]: (r1_tarski(A_1206, B_1207) | ~m1_subset_1(A_1206, k1_zfmisc_1(B_1207)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.04/3.23  tff(c_15737, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_15731, c_15733])).
% 9.04/3.23  tff(c_15811, plain, (![B_1217, A_1218]: (B_1217=A_1218 | ~r1_tarski(B_1217, A_1218) | ~r1_tarski(A_1218, B_1217))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.04/3.23  tff(c_15817, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_15737, c_15811])).
% 9.04/3.23  tff(c_15830, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15682, c_15817])).
% 9.04/3.23  tff(c_15679, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_15677, c_12])).
% 9.04/3.23  tff(c_15743, plain, (![A_1210]: (m1_subset_1(k6_relat_1(A_1210), k1_zfmisc_1(k2_zfmisc_1(A_1210, A_1210))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.04/3.23  tff(c_15750, plain, (m1_subset_1(k6_relat_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_15679, c_15743])).
% 9.04/3.23  tff(c_15771, plain, (r1_tarski(k6_relat_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_15750, c_16])).
% 9.04/3.23  tff(c_15815, plain, (k6_relat_1('#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k6_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_15771, c_15811])).
% 9.04/3.23  tff(c_15827, plain, (k6_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15682, c_15815])).
% 9.04/3.23  tff(c_15869, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15830, c_15830, c_15827])).
% 9.04/3.23  tff(c_15881, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_15869, c_28])).
% 9.04/3.23  tff(c_15847, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_15830, c_15682])).
% 9.04/3.23  tff(c_16297, plain, (![A_1269, B_1270, C_1271]: (k1_relset_1(A_1269, B_1270, C_1271)=k1_relat_1(C_1271) | ~m1_subset_1(C_1271, k1_zfmisc_1(k2_zfmisc_1(A_1269, B_1270))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.04/3.23  tff(c_16687, plain, (![A_1317, B_1318, A_1319]: (k1_relset_1(A_1317, B_1318, A_1319)=k1_relat_1(A_1319) | ~r1_tarski(A_1319, k2_zfmisc_1(A_1317, B_1318)))), inference(resolution, [status(thm)], [c_18, c_16297])).
% 9.04/3.23  tff(c_16701, plain, (![A_1317, B_1318]: (k1_relset_1(A_1317, B_1318, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_15847, c_16687])).
% 9.04/3.23  tff(c_16711, plain, (![A_1317, B_1318]: (k1_relset_1(A_1317, B_1318, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15881, c_16701])).
% 9.04/3.23  tff(c_15843, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15830, c_15731])).
% 9.04/3.23  tff(c_15850, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15830, c_15677])).
% 9.04/3.23  tff(c_70, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 9.04/3.23  tff(c_16802, plain, (![C_1330, B_1331]: (v1_funct_2(C_1330, '#skF_4', B_1331) | k1_relset_1('#skF_4', B_1331, C_1330)!='#skF_4' | ~m1_subset_1(C_1330, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_15850, c_15850, c_15850, c_15850, c_70])).
% 9.04/3.23  tff(c_16804, plain, (![B_1331]: (v1_funct_2('#skF_4', '#skF_4', B_1331) | k1_relset_1('#skF_4', B_1331, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_15843, c_16802])).
% 9.04/3.23  tff(c_16810, plain, (![B_1331]: (v1_funct_2('#skF_4', '#skF_4', B_1331))), inference(demodulation, [status(thm), theory('equality')], [c_16711, c_16804])).
% 9.04/3.23  tff(c_15774, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15731, c_15681, c_68])).
% 9.04/3.23  tff(c_15837, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15830, c_15774])).
% 9.04/3.23  tff(c_16815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16810, c_15837])).
% 9.04/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.04/3.23  
% 9.04/3.23  Inference rules
% 9.04/3.23  ----------------------
% 9.04/3.23  #Ref     : 0
% 9.04/3.23  #Sup     : 3431
% 9.04/3.23  #Fact    : 0
% 9.04/3.23  #Define  : 0
% 9.04/3.23  #Split   : 43
% 9.04/3.23  #Chain   : 0
% 9.04/3.23  #Close   : 0
% 9.04/3.23  
% 9.04/3.23  Ordering : KBO
% 9.04/3.23  
% 9.04/3.23  Simplification rules
% 9.04/3.23  ----------------------
% 9.04/3.23  #Subsume      : 927
% 9.04/3.23  #Demod        : 4167
% 9.04/3.23  #Tautology    : 1549
% 9.04/3.23  #SimpNegUnit  : 86
% 9.04/3.23  #BackRed      : 562
% 9.04/3.23  
% 9.04/3.23  #Partial instantiations: 0
% 9.04/3.23  #Strategies tried      : 1
% 9.04/3.23  
% 9.04/3.23  Timing (in seconds)
% 9.04/3.23  ----------------------
% 9.04/3.24  Preprocessing        : 0.32
% 9.04/3.24  Parsing              : 0.16
% 9.04/3.24  CNF conversion       : 0.02
% 9.04/3.24  Main loop            : 2.06
% 9.04/3.24  Inferencing          : 0.65
% 9.04/3.24  Reduction            : 0.76
% 9.04/3.24  Demodulation         : 0.55
% 9.04/3.24  BG Simplification    : 0.06
% 9.04/3.24  Subsumption          : 0.42
% 9.04/3.24  Abstraction          : 0.10
% 9.04/3.24  MUC search           : 0.00
% 9.04/3.24  Cooper               : 0.00
% 9.04/3.24  Total                : 2.45
% 9.04/3.24  Index Insertion      : 0.00
% 9.04/3.24  Index Deletion       : 0.00
% 9.04/3.24  Index Matching       : 0.00
% 9.04/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
