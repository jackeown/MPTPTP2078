%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:04 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 280 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 (1833 expanded)
%              Number of equality atoms :    6 (  95 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_276,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_137,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_233,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_184,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_38,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_99,plain,(
    ! [B_299,A_300] :
      ( v2_pre_topc(B_299)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_102,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_99])).

tff(c_105,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_102])).

tff(c_84,plain,(
    ! [B_293,A_294] :
      ( l1_pre_topc(B_293)
      | ~ m1_pre_topc(B_293,A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_90,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_87])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_145,plain,(
    ! [C_318,A_319,B_320] :
      ( m1_subset_1(C_318,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ m1_connsp_2(C_318,A_319,B_320)
      | ~ m1_subset_1(B_320,u1_struct_0(A_319))
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_148,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_182,plain,(
    ! [C_336,B_337,A_338] :
      ( r2_hidden(C_336,B_337)
      | ~ m1_connsp_2(B_337,A_338,C_336)
      | ~ m1_subset_1(C_336,u1_struct_0(A_338))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_186,plain,(
    ! [B_339,A_340] :
      ( r2_hidden(B_339,'#skF_1'(A_340,B_339))
      | ~ m1_subset_1('#skF_1'(A_340,B_339),k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ m1_subset_1(B_339,u1_struct_0(A_340))
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_20,c_182])).

tff(c_197,plain,(
    ! [B_346,A_347] :
      ( r2_hidden(B_346,'#skF_1'(A_347,B_346))
      | ~ m1_subset_1(B_346,u1_struct_0(A_347))
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_148,c_186])).

tff(c_149,plain,(
    ! [A_321,B_322] :
      ( m1_subset_1('#skF_1'(A_321,B_322),k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ m1_subset_1(B_322,u1_struct_0(A_321))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_10,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [A_321,A_5,B_322] :
      ( ~ v1_xboole_0(u1_struct_0(A_321))
      | ~ r2_hidden(A_5,'#skF_1'(A_321,B_322))
      | ~ m1_subset_1(B_322,u1_struct_0(A_321))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_149,c_10])).

tff(c_202,plain,(
    ! [A_348,B_349] :
      ( ~ v1_xboole_0(u1_struct_0(A_348))
      | ~ m1_subset_1(B_349,u1_struct_0(A_348))
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(resolution,[status(thm)],[c_197,c_152])).

tff(c_214,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_75,c_202])).

tff(c_223,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_90,c_214])).

tff(c_224,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_223])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_30,plain,(
    ! [B_44,A_42] :
      ( m1_subset_1(u1_struct_0(B_44),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_172,plain,(
    ! [B_332,A_333] :
      ( v3_pre_topc(u1_struct_0(B_332),A_333)
      | ~ v1_tsep_1(B_332,A_333)
      | ~ m1_subset_1(u1_struct_0(B_332),k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ m1_pre_topc(B_332,A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_176,plain,(
    ! [B_44,A_42] :
      ( v3_pre_topc(u1_struct_0(B_44),A_42)
      | ~ v1_tsep_1(B_44,A_42)
      | ~ v2_pre_topc(A_42)
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_77,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68])).

tff(c_116,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_52,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_74,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_276])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_74])).

tff(c_117,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_76])).

tff(c_228,plain,(
    ! [G_355,C_354,E_357,A_356,B_359,D_358] :
      ( r1_tmap_1(B_359,A_356,C_354,G_355)
      | ~ r1_tmap_1(D_358,A_356,k2_tmap_1(B_359,A_356,C_354,D_358),G_355)
      | ~ r1_tarski(E_357,u1_struct_0(D_358))
      | ~ r2_hidden(G_355,E_357)
      | ~ v3_pre_topc(E_357,B_359)
      | ~ m1_subset_1(G_355,u1_struct_0(D_358))
      | ~ m1_subset_1(G_355,u1_struct_0(B_359))
      | ~ m1_subset_1(E_357,k1_zfmisc_1(u1_struct_0(B_359)))
      | ~ m1_pre_topc(D_358,B_359)
      | v2_struct_0(D_358)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_359),u1_struct_0(A_356))))
      | ~ v1_funct_2(C_354,u1_struct_0(B_359),u1_struct_0(A_356))
      | ~ v1_funct_1(C_354)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_232,plain,(
    ! [E_357] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ r1_tarski(E_357,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',E_357)
      | ~ v3_pre_topc(E_357,'#skF_3')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_357,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_117,c_228])).

tff(c_239,plain,(
    ! [E_357] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ r1_tarski(E_357,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',E_357)
      | ~ v3_pre_topc(E_357,'#skF_3')
      | ~ m1_subset_1(E_357,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_50,c_44,c_42,c_75,c_232])).

tff(c_241,plain,(
    ! [E_360] :
      ( ~ r1_tarski(E_360,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',E_360)
      | ~ v3_pre_topc(E_360,'#skF_3')
      | ~ m1_subset_1(E_360,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_48,c_116,c_239])).

tff(c_249,plain,(
    ! [B_44] :
      ( ~ r1_tarski(u1_struct_0(B_44),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_44))
      | ~ v3_pre_topc(u1_struct_0(B_44),'#skF_3')
      | ~ m1_pre_topc(B_44,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_241])).

tff(c_257,plain,(
    ! [B_361] :
      ( ~ r1_tarski(u1_struct_0(B_361),u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_361))
      | ~ v3_pre_topc(u1_struct_0(B_361),'#skF_3')
      | ~ m1_pre_topc(B_361,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_249])).

tff(c_261,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_264,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_261])).

tff(c_265,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_268,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_265])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_58,c_46,c_268])).

tff(c_273,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_284,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8,c_273])).

tff(c_287,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_284])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_287])).

tff(c_291,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_362,plain,(
    ! [B_393,C_396,A_395,F_397,D_394] :
      ( r1_tmap_1(D_394,A_395,k2_tmap_1(B_393,A_395,C_396,D_394),F_397)
      | ~ r1_tmap_1(B_393,A_395,C_396,F_397)
      | ~ m1_subset_1(F_397,u1_struct_0(D_394))
      | ~ m1_subset_1(F_397,u1_struct_0(B_393))
      | ~ m1_pre_topc(D_394,B_393)
      | v2_struct_0(D_394)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_393),u1_struct_0(A_395))))
      | ~ v1_funct_2(C_396,u1_struct_0(B_393),u1_struct_0(A_395))
      | ~ v1_funct_1(C_396)
      | ~ l1_pre_topc(B_393)
      | ~ v2_pre_topc(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_364,plain,(
    ! [D_394,F_397] :
      ( r1_tmap_1(D_394,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_394),F_397)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_397)
      | ~ m1_subset_1(F_397,u1_struct_0(D_394))
      | ~ m1_subset_1(F_397,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_394,'#skF_3')
      | v2_struct_0(D_394)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_362])).

tff(c_367,plain,(
    ! [D_394,F_397] :
      ( r1_tmap_1(D_394,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_394),F_397)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_397)
      | ~ m1_subset_1(F_397,u1_struct_0(D_394))
      | ~ m1_subset_1(F_397,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_394,'#skF_3')
      | v2_struct_0(D_394)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_364])).

tff(c_404,plain,(
    ! [D_412,F_413] :
      ( r1_tmap_1(D_412,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_412),F_413)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_413)
      | ~ m1_subset_1(F_413,u1_struct_0(D_412))
      | ~ m1_subset_1(F_413,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_412,'#skF_3')
      | v2_struct_0(D_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_367])).

tff(c_290,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_409,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_404,c_290])).

tff(c_416,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_75,c_291,c_409])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:48:39 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.52  
% 3.16/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.52  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.16/1.52  
% 3.16/1.52  %Foreground sorts:
% 3.16/1.52  
% 3.16/1.52  
% 3.16/1.52  %Background operators:
% 3.16/1.52  
% 3.16/1.52  
% 3.16/1.52  %Foreground operators:
% 3.16/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.16/1.52  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.16/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.52  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.52  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.16/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.16/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.52  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.16/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.16/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.16/1.52  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.16/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.52  
% 3.43/1.54  tff(f_276, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.43/1.54  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.43/1.54  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.43/1.54  tff(f_102, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.43/1.54  tff(f_90, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.43/1.54  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 3.43/1.54  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.43/1.54  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.43/1.54  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.43/1.54  tff(f_137, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.43/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.43/1.54  tff(f_233, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.43/1.54  tff(f_184, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.43/1.54  tff(c_48, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_38, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 3.43/1.54  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_99, plain, (![B_299, A_300]: (v2_pre_topc(B_299) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.43/1.54  tff(c_102, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_99])).
% 3.43/1.54  tff(c_105, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_102])).
% 3.43/1.54  tff(c_84, plain, (![B_293, A_294]: (l1_pre_topc(B_293) | ~m1_pre_topc(B_293, A_294) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.43/1.54  tff(c_87, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_84])).
% 3.43/1.54  tff(c_90, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_87])).
% 3.43/1.54  tff(c_20, plain, (![A_25, B_26]: (m1_connsp_2('#skF_1'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.43/1.54  tff(c_145, plain, (![C_318, A_319, B_320]: (m1_subset_1(C_318, k1_zfmisc_1(u1_struct_0(A_319))) | ~m1_connsp_2(C_318, A_319, B_320) | ~m1_subset_1(B_320, u1_struct_0(A_319)) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.43/1.54  tff(c_148, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_20, c_145])).
% 3.43/1.54  tff(c_182, plain, (![C_336, B_337, A_338]: (r2_hidden(C_336, B_337) | ~m1_connsp_2(B_337, A_338, C_336) | ~m1_subset_1(C_336, u1_struct_0(A_338)) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(A_338))) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338) | v2_struct_0(A_338))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.43/1.54  tff(c_186, plain, (![B_339, A_340]: (r2_hidden(B_339, '#skF_1'(A_340, B_339)) | ~m1_subset_1('#skF_1'(A_340, B_339), k1_zfmisc_1(u1_struct_0(A_340))) | ~m1_subset_1(B_339, u1_struct_0(A_340)) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(resolution, [status(thm)], [c_20, c_182])).
% 3.43/1.54  tff(c_197, plain, (![B_346, A_347]: (r2_hidden(B_346, '#skF_1'(A_347, B_346)) | ~m1_subset_1(B_346, u1_struct_0(A_347)) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(resolution, [status(thm)], [c_148, c_186])).
% 3.43/1.54  tff(c_149, plain, (![A_321, B_322]: (m1_subset_1('#skF_1'(A_321, B_322), k1_zfmisc_1(u1_struct_0(A_321))) | ~m1_subset_1(B_322, u1_struct_0(A_321)) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_20, c_145])).
% 3.43/1.54  tff(c_10, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.54  tff(c_152, plain, (![A_321, A_5, B_322]: (~v1_xboole_0(u1_struct_0(A_321)) | ~r2_hidden(A_5, '#skF_1'(A_321, B_322)) | ~m1_subset_1(B_322, u1_struct_0(A_321)) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_149, c_10])).
% 3.43/1.54  tff(c_202, plain, (![A_348, B_349]: (~v1_xboole_0(u1_struct_0(A_348)) | ~m1_subset_1(B_349, u1_struct_0(A_348)) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348) | v2_struct_0(A_348))), inference(resolution, [status(thm)], [c_197, c_152])).
% 3.43/1.54  tff(c_214, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_75, c_202])).
% 3.43/1.54  tff(c_223, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_90, c_214])).
% 3.43/1.54  tff(c_224, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_223])).
% 3.43/1.54  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.54  tff(c_46, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_30, plain, (![B_44, A_42]: (m1_subset_1(u1_struct_0(B_44), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.43/1.54  tff(c_172, plain, (![B_332, A_333]: (v3_pre_topc(u1_struct_0(B_332), A_333) | ~v1_tsep_1(B_332, A_333) | ~m1_subset_1(u1_struct_0(B_332), k1_zfmisc_1(u1_struct_0(A_333))) | ~m1_pre_topc(B_332, A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.43/1.54  tff(c_176, plain, (![B_44, A_42]: (v3_pre_topc(u1_struct_0(B_44), A_42) | ~v1_tsep_1(B_44, A_42) | ~v2_pre_topc(A_42) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_30, c_172])).
% 3.43/1.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.54  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_68, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_77, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68])).
% 3.43/1.54  tff(c_116, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_77])).
% 3.43/1.54  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_52, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_74, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_276])).
% 3.43/1.54  tff(c_76, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_74])).
% 3.43/1.54  tff(c_117, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_116, c_76])).
% 3.43/1.54  tff(c_228, plain, (![G_355, C_354, E_357, A_356, B_359, D_358]: (r1_tmap_1(B_359, A_356, C_354, G_355) | ~r1_tmap_1(D_358, A_356, k2_tmap_1(B_359, A_356, C_354, D_358), G_355) | ~r1_tarski(E_357, u1_struct_0(D_358)) | ~r2_hidden(G_355, E_357) | ~v3_pre_topc(E_357, B_359) | ~m1_subset_1(G_355, u1_struct_0(D_358)) | ~m1_subset_1(G_355, u1_struct_0(B_359)) | ~m1_subset_1(E_357, k1_zfmisc_1(u1_struct_0(B_359))) | ~m1_pre_topc(D_358, B_359) | v2_struct_0(D_358) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_359), u1_struct_0(A_356)))) | ~v1_funct_2(C_354, u1_struct_0(B_359), u1_struct_0(A_356)) | ~v1_funct_1(C_354) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356))), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.43/1.54  tff(c_232, plain, (![E_357]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~r1_tarski(E_357, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', E_357) | ~v3_pre_topc(E_357, '#skF_3') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_357, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_117, c_228])).
% 3.43/1.54  tff(c_239, plain, (![E_357]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~r1_tarski(E_357, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', E_357) | ~v3_pre_topc(E_357, '#skF_3') | ~m1_subset_1(E_357, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_50, c_44, c_42, c_75, c_232])).
% 3.43/1.54  tff(c_241, plain, (![E_360]: (~r1_tarski(E_360, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', E_360) | ~v3_pre_topc(E_360, '#skF_3') | ~m1_subset_1(E_360, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_48, c_116, c_239])).
% 3.43/1.54  tff(c_249, plain, (![B_44]: (~r1_tarski(u1_struct_0(B_44), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', u1_struct_0(B_44)) | ~v3_pre_topc(u1_struct_0(B_44), '#skF_3') | ~m1_pre_topc(B_44, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_241])).
% 3.43/1.54  tff(c_257, plain, (![B_361]: (~r1_tarski(u1_struct_0(B_361), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', u1_struct_0(B_361)) | ~v3_pre_topc(u1_struct_0(B_361), '#skF_3') | ~m1_pre_topc(B_361, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_249])).
% 3.43/1.54  tff(c_261, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_257])).
% 3.43/1.54  tff(c_264, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_261])).
% 3.43/1.54  tff(c_265, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_264])).
% 3.43/1.54  tff(c_268, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_176, c_265])).
% 3.43/1.54  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_58, c_46, c_268])).
% 3.43/1.54  tff(c_273, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_264])).
% 3.43/1.54  tff(c_284, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8, c_273])).
% 3.43/1.54  tff(c_287, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_284])).
% 3.43/1.54  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_287])).
% 3.43/1.54  tff(c_291, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 3.43/1.54  tff(c_362, plain, (![B_393, C_396, A_395, F_397, D_394]: (r1_tmap_1(D_394, A_395, k2_tmap_1(B_393, A_395, C_396, D_394), F_397) | ~r1_tmap_1(B_393, A_395, C_396, F_397) | ~m1_subset_1(F_397, u1_struct_0(D_394)) | ~m1_subset_1(F_397, u1_struct_0(B_393)) | ~m1_pre_topc(D_394, B_393) | v2_struct_0(D_394) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_393), u1_struct_0(A_395)))) | ~v1_funct_2(C_396, u1_struct_0(B_393), u1_struct_0(A_395)) | ~v1_funct_1(C_396) | ~l1_pre_topc(B_393) | ~v2_pre_topc(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_184])).
% 3.43/1.54  tff(c_364, plain, (![D_394, F_397]: (r1_tmap_1(D_394, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_394), F_397) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_397) | ~m1_subset_1(F_397, u1_struct_0(D_394)) | ~m1_subset_1(F_397, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_394, '#skF_3') | v2_struct_0(D_394) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_362])).
% 3.43/1.54  tff(c_367, plain, (![D_394, F_397]: (r1_tmap_1(D_394, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_394), F_397) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_397) | ~m1_subset_1(F_397, u1_struct_0(D_394)) | ~m1_subset_1(F_397, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_394, '#skF_3') | v2_struct_0(D_394) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_58, c_56, c_54, c_52, c_364])).
% 3.43/1.54  tff(c_404, plain, (![D_412, F_413]: (r1_tmap_1(D_412, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_412), F_413) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_413) | ~m1_subset_1(F_413, u1_struct_0(D_412)) | ~m1_subset_1(F_413, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_412, '#skF_3') | v2_struct_0(D_412))), inference(negUnitSimplification, [status(thm)], [c_66, c_60, c_367])).
% 3.43/1.54  tff(c_290, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_77])).
% 3.43/1.54  tff(c_409, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_404, c_290])).
% 3.43/1.54  tff(c_416, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_75, c_291, c_409])).
% 3.43/1.54  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_416])).
% 3.43/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.54  
% 3.43/1.54  Inference rules
% 3.43/1.54  ----------------------
% 3.43/1.54  #Ref     : 0
% 3.43/1.54  #Sup     : 57
% 3.43/1.54  #Fact    : 0
% 3.43/1.54  #Define  : 0
% 3.43/1.54  #Split   : 3
% 3.43/1.54  #Chain   : 0
% 3.43/1.54  #Close   : 0
% 3.43/1.54  
% 3.43/1.54  Ordering : KBO
% 3.43/1.54  
% 3.43/1.54  Simplification rules
% 3.43/1.54  ----------------------
% 3.43/1.54  #Subsume      : 11
% 3.43/1.54  #Demod        : 82
% 3.43/1.54  #Tautology    : 17
% 3.43/1.54  #SimpNegUnit  : 22
% 3.43/1.54  #BackRed      : 0
% 3.43/1.54  
% 3.43/1.54  #Partial instantiations: 0
% 3.43/1.54  #Strategies tried      : 1
% 3.43/1.54  
% 3.43/1.54  Timing (in seconds)
% 3.43/1.54  ----------------------
% 3.43/1.55  Preprocessing        : 0.40
% 3.43/1.55  Parsing              : 0.21
% 3.43/1.55  CNF conversion       : 0.05
% 3.43/1.55  Main loop            : 0.31
% 3.43/1.55  Inferencing          : 0.11
% 3.43/1.55  Reduction            : 0.09
% 3.43/1.55  Demodulation         : 0.07
% 3.43/1.55  BG Simplification    : 0.02
% 3.43/1.55  Subsumption          : 0.06
% 3.43/1.55  Abstraction          : 0.01
% 3.43/1.55  MUC search           : 0.00
% 3.43/1.55  Cooper               : 0.00
% 3.43/1.55  Total                : 0.75
% 3.43/1.55  Index Insertion      : 0.00
% 3.43/1.55  Index Deletion       : 0.00
% 3.43/1.55  Index Matching       : 0.00
% 3.43/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
