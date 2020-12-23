%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:18 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 464 expanded)
%              Number of leaves         :   29 ( 166 expanded)
%              Depth                    :   12
%              Number of atoms          :  233 (1747 expanded)
%              Number of equality atoms :   12 (  92 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_64,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_54,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_66,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_179,plain,(
    ! [A_64,B_65] :
      ( '#skF_3'(A_64,B_65) != B_65
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_190,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_179])).

tff(c_195,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_190])).

tff(c_196,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_195])).

tff(c_197,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_454,plain,(
    ! [B_100,A_101] :
      ( v2_tex_2(B_100,A_101)
      | ~ v1_zfmisc_1(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | v1_xboole_0(B_100)
      | ~ l1_pre_topc(A_101)
      | ~ v2_tdlat_3(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_468,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_454])).

tff(c_474,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_64,c_468])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_197,c_474])).

tff(c_477,plain,(
    '#skF_3'('#skF_4','#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_478,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_576,plain,(
    ! [B_121,A_122] :
      ( r1_tarski(B_121,'#skF_3'(A_122,B_121))
      | v3_tex_2(B_121,A_122)
      | ~ v2_tex_2(B_121,A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_584,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_576])).

tff(c_589,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_478,c_584])).

tff(c_590,plain,(
    r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_589])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_612,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_590,c_6])).

tff(c_619,plain,(
    ~ r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_612])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_174,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_2'(A_61,B_62,C_63),B_62)
      | r1_tarski(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_479,plain,(
    ! [B_102,C_103,A_104] :
      ( ~ v1_xboole_0(B_102)
      | r1_tarski(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_104)) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_537,plain,(
    ! [B_112,A_113,B_114] :
      ( ~ v1_xboole_0(B_112)
      | r1_tarski(B_112,A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(B_114))
      | ~ r1_tarski(A_113,B_114) ) ),
    inference(resolution,[status(thm)],[c_20,c_479])).

tff(c_546,plain,(
    ! [A_14,A_113,B_15] :
      ( ~ v1_xboole_0(A_14)
      | r1_tarski(A_14,A_113)
      | ~ r1_tarski(A_113,B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_537])).

tff(c_621,plain,(
    ! [A_125] :
      ( ~ v1_xboole_0(A_125)
      | r1_tarski(A_125,'#skF_5')
      | ~ r1_tarski(A_125,'#skF_3'('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_590,c_546])).

tff(c_628,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_621])).

tff(c_633,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_628])).

tff(c_34,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_610,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_590,c_34])).

tff(c_616,plain,
    ( ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_477,c_610])).

tff(c_620,plain,(
    ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_591,plain,(
    ! [A_123,B_124] :
      ( v2_tex_2('#skF_3'(A_123,B_124),A_123)
      | v3_tex_2(B_124,A_123)
      | ~ v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_599,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_591])).

tff(c_604,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_478,c_599])).

tff(c_605,plain,(
    v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_604])).

tff(c_740,plain,(
    ! [A_144,B_145] :
      ( m1_subset_1('#skF_3'(A_144,B_145),k1_zfmisc_1(u1_struct_0(A_144)))
      | v3_tex_2(B_145,A_144)
      | ~ v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [B_34,A_32] :
      ( v1_zfmisc_1(B_34)
      | ~ v2_tex_2(B_34,A_32)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | v1_xboole_0(B_34)
      | ~ l1_pre_topc(A_32)
      | ~ v2_tdlat_3(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1375,plain,(
    ! [A_214,B_215] :
      ( v1_zfmisc_1('#skF_3'(A_214,B_215))
      | ~ v2_tex_2('#skF_3'(A_214,B_215),A_214)
      | v1_xboole_0('#skF_3'(A_214,B_215))
      | ~ v2_tdlat_3(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214)
      | v3_tex_2(B_215,A_214)
      | ~ v2_tex_2(B_215,A_214)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(resolution,[status(thm)],[c_740,c_40])).

tff(c_1383,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_605,c_1375])).

tff(c_1389,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_478,c_50,c_48,c_1383])).

tff(c_1391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_52,c_633,c_620,c_1389])).

tff(c_1392,plain,(
    v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_1394,plain,(
    ! [A_216] :
      ( ~ v1_xboole_0(A_216)
      | r1_tarski(A_216,'#skF_5')
      | ~ r1_tarski(A_216,'#skF_3'('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_590,c_546])).

tff(c_1401,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1394])).

tff(c_1406,plain,(
    r1_tarski('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_1401])).

tff(c_1408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_1406])).

tff(c_1410,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1409,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1452,plain,(
    ! [B_226,A_227] :
      ( v2_tex_2(B_226,A_227)
      | ~ v3_tex_2(B_226,A_227)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1459,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1452])).

tff(c_1463,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1409,c_1459])).

tff(c_1686,plain,(
    ! [B_272,A_273] :
      ( v1_zfmisc_1(B_272)
      | ~ v2_tex_2(B_272,A_273)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_273)))
      | v1_xboole_0(B_272)
      | ~ l1_pre_topc(A_273)
      | ~ v2_tdlat_3(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1697,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1686])).

tff(c_1702,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1463,c_1697])).

tff(c_1704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_44,c_1410,c_1702])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.72  
% 4.37/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.72  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.37/1.72  
% 4.37/1.72  %Foreground sorts:
% 4.37/1.72  
% 4.37/1.72  
% 4.37/1.72  %Background operators:
% 4.37/1.72  
% 4.37/1.72  
% 4.37/1.72  %Foreground operators:
% 4.37/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.37/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.37/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.37/1.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.37/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.72  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.37/1.72  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.37/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.37/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.72  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.37/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.37/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/1.72  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.37/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.72  
% 4.37/1.74  tff(f_139, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 4.37/1.74  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.37/1.74  tff(f_119, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 4.37/1.74  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.37/1.74  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.37/1.74  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 4.37/1.74  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.37/1.74  tff(f_86, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.37/1.74  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_44, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_60, plain, (v3_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_64, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 4.37/1.74  tff(c_54, plain, (~v1_zfmisc_1('#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_66, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54])).
% 4.37/1.74  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_179, plain, (![A_64, B_65]: ('#skF_3'(A_64, B_65)!=B_65 | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.37/1.74  tff(c_190, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_179])).
% 4.37/1.74  tff(c_195, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_190])).
% 4.37/1.74  tff(c_196, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_195])).
% 4.37/1.74  tff(c_197, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_196])).
% 4.37/1.74  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_48, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.37/1.74  tff(c_454, plain, (![B_100, A_101]: (v2_tex_2(B_100, A_101) | ~v1_zfmisc_1(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | v1_xboole_0(B_100) | ~l1_pre_topc(A_101) | ~v2_tdlat_3(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.37/1.74  tff(c_468, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_454])).
% 4.37/1.74  tff(c_474, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_64, c_468])).
% 4.37/1.74  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_197, c_474])).
% 4.37/1.74  tff(c_477, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_196])).
% 4.37/1.74  tff(c_478, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_196])).
% 4.37/1.74  tff(c_576, plain, (![B_121, A_122]: (r1_tarski(B_121, '#skF_3'(A_122, B_121)) | v3_tex_2(B_121, A_122) | ~v2_tex_2(B_121, A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.37/1.74  tff(c_584, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_576])).
% 4.37/1.74  tff(c_589, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_478, c_584])).
% 4.37/1.74  tff(c_590, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_589])).
% 4.37/1.74  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.74  tff(c_612, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_590, c_6])).
% 4.37/1.74  tff(c_619, plain, (~r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_477, c_612])).
% 4.37/1.74  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/1.74  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.37/1.74  tff(c_174, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_2'(A_61, B_62, C_63), B_62) | r1_tarski(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.37/1.74  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/1.74  tff(c_479, plain, (![B_102, C_103, A_104]: (~v1_xboole_0(B_102) | r1_tarski(B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_104)))), inference(resolution, [status(thm)], [c_174, c_2])).
% 4.37/1.74  tff(c_537, plain, (![B_112, A_113, B_114]: (~v1_xboole_0(B_112) | r1_tarski(B_112, A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(B_114)) | ~r1_tarski(A_113, B_114))), inference(resolution, [status(thm)], [c_20, c_479])).
% 4.37/1.74  tff(c_546, plain, (![A_14, A_113, B_15]: (~v1_xboole_0(A_14) | r1_tarski(A_14, A_113) | ~r1_tarski(A_113, B_15) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_20, c_537])).
% 4.37/1.74  tff(c_621, plain, (![A_125]: (~v1_xboole_0(A_125) | r1_tarski(A_125, '#skF_5') | ~r1_tarski(A_125, '#skF_3'('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_590, c_546])).
% 4.37/1.74  tff(c_628, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_10, c_621])).
% 4.37/1.74  tff(c_633, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_619, c_628])).
% 4.37/1.74  tff(c_34, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.37/1.74  tff(c_610, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_590, c_34])).
% 4.37/1.74  tff(c_616, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_44, c_477, c_610])).
% 4.37/1.74  tff(c_620, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_616])).
% 4.37/1.74  tff(c_591, plain, (![A_123, B_124]: (v2_tex_2('#skF_3'(A_123, B_124), A_123) | v3_tex_2(B_124, A_123) | ~v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.37/1.74  tff(c_599, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_591])).
% 4.37/1.74  tff(c_604, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_478, c_599])).
% 4.37/1.74  tff(c_605, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_604])).
% 4.37/1.74  tff(c_740, plain, (![A_144, B_145]: (m1_subset_1('#skF_3'(A_144, B_145), k1_zfmisc_1(u1_struct_0(A_144))) | v3_tex_2(B_145, A_144) | ~v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.37/1.74  tff(c_40, plain, (![B_34, A_32]: (v1_zfmisc_1(B_34) | ~v2_tex_2(B_34, A_32) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_32))) | v1_xboole_0(B_34) | ~l1_pre_topc(A_32) | ~v2_tdlat_3(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.37/1.74  tff(c_1375, plain, (![A_214, B_215]: (v1_zfmisc_1('#skF_3'(A_214, B_215)) | ~v2_tex_2('#skF_3'(A_214, B_215), A_214) | v1_xboole_0('#skF_3'(A_214, B_215)) | ~v2_tdlat_3(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214) | v3_tex_2(B_215, A_214) | ~v2_tex_2(B_215, A_214) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(resolution, [status(thm)], [c_740, c_40])).
% 4.37/1.74  tff(c_1383, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_605, c_1375])).
% 4.37/1.74  tff(c_1389, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_478, c_50, c_48, c_1383])).
% 4.37/1.74  tff(c_1391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_52, c_633, c_620, c_1389])).
% 4.37/1.74  tff(c_1392, plain, (v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_616])).
% 4.37/1.74  tff(c_1394, plain, (![A_216]: (~v1_xboole_0(A_216) | r1_tarski(A_216, '#skF_5') | ~r1_tarski(A_216, '#skF_3'('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_590, c_546])).
% 4.37/1.74  tff(c_1401, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_10, c_1394])).
% 4.37/1.74  tff(c_1406, plain, (r1_tarski('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1392, c_1401])).
% 4.37/1.74  tff(c_1408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_619, c_1406])).
% 4.37/1.74  tff(c_1410, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 4.37/1.74  tff(c_1409, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 4.37/1.74  tff(c_1452, plain, (![B_226, A_227]: (v2_tex_2(B_226, A_227) | ~v3_tex_2(B_226, A_227) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.37/1.74  tff(c_1459, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1452])).
% 4.37/1.74  tff(c_1463, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1409, c_1459])).
% 4.37/1.74  tff(c_1686, plain, (![B_272, A_273]: (v1_zfmisc_1(B_272) | ~v2_tex_2(B_272, A_273) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_273))) | v1_xboole_0(B_272) | ~l1_pre_topc(A_273) | ~v2_tdlat_3(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.37/1.74  tff(c_1697, plain, (v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1686])).
% 4.37/1.74  tff(c_1702, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1463, c_1697])).
% 4.37/1.74  tff(c_1704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_44, c_1410, c_1702])).
% 4.37/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.74  
% 4.37/1.74  Inference rules
% 4.37/1.74  ----------------------
% 4.37/1.74  #Ref     : 0
% 4.37/1.74  #Sup     : 328
% 4.37/1.74  #Fact    : 0
% 4.37/1.74  #Define  : 0
% 4.37/1.74  #Split   : 10
% 4.37/1.74  #Chain   : 0
% 4.37/1.74  #Close   : 0
% 4.37/1.74  
% 4.37/1.74  Ordering : KBO
% 4.37/1.74  
% 4.37/1.74  Simplification rules
% 4.37/1.74  ----------------------
% 4.37/1.74  #Subsume      : 66
% 4.37/1.74  #Demod        : 152
% 4.37/1.74  #Tautology    : 50
% 4.37/1.74  #SimpNegUnit  : 49
% 4.37/1.74  #BackRed      : 0
% 4.37/1.74  
% 4.37/1.74  #Partial instantiations: 0
% 4.37/1.74  #Strategies tried      : 1
% 4.37/1.74  
% 4.37/1.74  Timing (in seconds)
% 4.37/1.74  ----------------------
% 4.37/1.74  Preprocessing        : 0.30
% 4.37/1.74  Parsing              : 0.16
% 4.37/1.74  CNF conversion       : 0.02
% 4.37/1.74  Main loop            : 0.69
% 4.37/1.74  Inferencing          : 0.24
% 4.37/1.74  Reduction            : 0.18
% 4.37/1.74  Demodulation         : 0.12
% 4.37/1.74  BG Simplification    : 0.03
% 4.37/1.74  Subsumption          : 0.19
% 4.37/1.74  Abstraction          : 0.03
% 4.37/1.74  MUC search           : 0.00
% 4.37/1.74  Cooper               : 0.00
% 4.37/1.74  Total                : 1.03
% 4.37/1.74  Index Insertion      : 0.00
% 4.37/1.74  Index Deletion       : 0.00
% 4.37/1.74  Index Matching       : 0.00
% 4.37/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
