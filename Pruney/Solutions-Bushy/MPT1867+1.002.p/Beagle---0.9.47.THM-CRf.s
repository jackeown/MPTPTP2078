%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1867+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:34 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 183 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_66,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_218,plain,(
    ! [B_68,A_69] :
      ( v3_pre_topc(B_68,A_69)
      | ~ v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_229,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_218])).

tff(c_240,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_229])).

tff(c_304,plain,(
    ! [A_77,B_78] :
      ( r1_tarski('#skF_2'(A_77,B_78),B_78)
      | v2_tex_2(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_315,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_304])).

tff(c_324,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_315])).

tff(c_325,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_324])).

tff(c_24,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,(
    ! [B_51,A_52] :
      ( v1_xboole_0(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_37,B_38] :
      ( v1_xboole_0(A_37)
      | ~ v1_xboole_0(B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_329,plain,
    ( v1_xboole_0('#skF_2'('#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_325,c_77])).

tff(c_332,plain,(
    v1_xboole_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_329])).

tff(c_40,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    ! [A_44] :
      ( A_44 = '#skF_5'
      | ~ v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_32,c_40])).

tff(c_357,plain,(
    '#skF_2'('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_332,c_43])).

tff(c_18,plain,(
    ! [A_32] : m1_subset_1('#skF_3'(A_32),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_89,plain,(
    ! [A_54,B_55,C_56] :
      ( k9_subset_1(A_54,B_55,B_55) = B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_98,plain,(
    ! [A_54,B_55] : k9_subset_1(A_54,B_55,B_55) = B_55 ),
    inference(resolution,[status(thm)],[c_18,c_89])).

tff(c_615,plain,(
    ! [A_100,B_101,D_102] :
      ( k9_subset_1(u1_struct_0(A_100),B_101,D_102) != '#skF_2'(A_100,B_101)
      | ~ v3_pre_topc(D_102,A_100)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(u1_struct_0(A_100)))
      | v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1686,plain,(
    ! [A_173,B_174] :
      ( '#skF_2'(A_173,B_174) != B_174
      | ~ v3_pre_topc(B_174,A_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | v2_tex_2(B_174,A_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_615])).

tff(c_1701,plain,
    ( '#skF_2'('#skF_4','#skF_5') != '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1686])).

tff(c_1712,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_240,c_357,c_1701])).

tff(c_1714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1712])).

%------------------------------------------------------------------------------
